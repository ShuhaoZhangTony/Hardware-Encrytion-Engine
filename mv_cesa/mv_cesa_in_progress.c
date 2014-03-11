#include "crypto/algapi.h"
#include "linux/crypto.h"
#include "linux/interrupt.h"
#include "linux/io.h"
#include "linux/kthread.h"
#include "linux/platform_device.h"
#include "linux/scatterlist.h"
#include "linux/slab.h"
#include "linux/module.h"
#include "crypto/internal/hash.h"
#include "crypto/sha.h"
#include <linux/pci.h>
#include "mv_cesa.h"
#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/pci.h>
#include <linux/pci_ids.h>
#include <linux/crypto.h>
#include <linux/spinlock.h>
#include <crypto/algapi.h>
#include <crypto/aes.h>
#include <linux/time.h>
#include <linux/io.h>
#include <linux/delay.h>
//#include "dsi-aes.h"
#define numOfCpg 5 
#define MV_CESA	"MV-CESA:"
#define MAX_HW_HASH_SIZE	0xFFFF
#define DMA_REGISTER_SIZE         (4 * DREGCOUNT)    // There are eighteen registers, and each is 4 bytes wide.

#define DMEM32(val, len)	do { 								\
					int iCtr; 						\
					for (iCtr = 0; iCtr < len; iCtr += 4) { 		\
						if ((iCtr % 16) == 0) 				\
							printk("\r\n\t"); 			\
						printk("%08x ", cpu_to_be32(*(unsigned long *)(val + iCtr)));\
					} 							\
				} while(0)



#define DSI_DMA_ENABLE
// #define DSI_AES_ALG_ENABLE
#define DSI_AES_ECB_ENABLE
// #define DSI_AES_CBC_ENABLE

#define DSI_HW_CRYPT_VENDOR_ID		0x10EE
#define DSI_HW_CRYPT_DEVICE_ID		0x6018
#define DSI_HW_CRYPT_SUBVENDOR_ID 	0x10EE
#define DSI_HW_CRYPT_SUBDEVICE_ID 	0x0007

#define HAVE_REGION 0x01                    // I/O Memory region
#define HAVE_IRQ    0x02                    // Interupt
#define HAVE_KREG   0x04                    // Kernel registration

#define BUF_SIZE		4096

#define DMA_WRITE_START		0x00000001	
#define DMA_WR_RELAX_ORDER	0x00000020
#define DMA_WR_NO_SNOOP		0x00000040
#define DMA_WINTR_DISABLE 	0x00000080
#define DMA_WRITE_DONE		0x00000100

#define DMA_READ_START 		0x00010000
#define DMA_RD_RELAX_ORDER	0x00200000
#define DMA_RD_NO_SNOOP		0x00400000
#define DMA_RINTR_DISABLE	0x00800000
#define DMA_READ_DONE		0x01000000

#define DCSR_READ_DONE	0x04
#define DCSR_WRITE_DONE 0x02
#define RDMATLPS_START_OP 	0x80000000
#define AES_DIR_ENC		0x00000000
#define AES_DIR_DEC		0x40000000

#define DCSR            0x28
#define RDMATLPSA       0x0C
#define RDMATLPS        0x1C
#define WDMATLPDA       0x04
#define WDMATLPS        0x18
#define STATUSREG       0x50
#define AESKEY0_0	0x60 /* AES key MSW */
#define ICSR            0x40
#define ICLR            0x48

#define DREGCOUNT 18
#define DMA_REGISTER_SIZE         (4 * DREGCOUNT)    // There are eighteen registers, and each is 4 bytes wide.

/* Static structures */
typedef struct
dma_mem_struct
{
	unsigned long addr;
	unsigned long size;
	void __iomem  *map;
}	dma_mem_t;

static dma_mem_t dsi_aes_dma;
static spinlock_t lock;
static unsigned long stat_flags = 0;
static unsigned char *wr_buf = NULL, *rd_buf = NULL, *unaligned_buf = NULL;
static dma_addr_t rd_hw_addr, wr_hw_addr;
static int key_size;

/*
 * STM:
 *   /-----------------------------------------------------\
 *   |			|-----------|					  			| 
 *  \./			\./		 	|					 			|
 * IDLE -> new request->collect 8 -> BUSY -> done -> DEQUEUE  request complete
 *			   
 *			    
 */
enum engine_status {
	ENGINE_IDLE,
	ENGINE_BUSY,
	ENGINE_W_DEQUEUE,
};

/**
 * struct req_progress - used for every crypt request
 * @src_sg_it:		sg iterator for src
 * @dst_sg_it:		sg iterator for dst
 * @sg_src_left:	bytes left in src to process (scatter list)
 * @src_start:		offset to add to src start position (scatter list)
 * @crypt_len:		length of current hw crypt/hash process
 * @hw_nbytes:		total bytes to process in hw for this request
 * @copy_back:		whether to copy data back (crypt) or not (hash)
 * @sg_dst_left:	bytes left dst to process in this scatter list
 * @dst_start:		ofset to add to dst start position (scatter list)
 * @hw_processed_bytes:	number of bytes processed by hw (request).
 *
 * sg helper are used to iterate over the scatterlist. Since the size of the
 * SRAM may be less than the scatter size, this struct is used to keep
 * track of progress within current scatterlist.
 */
struct req_progress {
	struct sg_mapping_iter src_sg_it;
	struct sg_mapping_iter dst_sg_it;
	void (*complete) (int id);
	void (*process) (int is_first);

	/* src mostly */
	int sg_src_left;
	int src_start;
	int hw_nbytes;//total bytes to process in hw for this request
	/* dst mostly */
	int sg_dst_left;
	int dst_start;
};

struct crypto_priv {
	/**critical members*/
	struct crypto_async_request *request_collector[10];//this array is used to store address of request
	struct task_struct *queue_th;
	struct task_struct *interrupt_th;
	unsigned char sourceBuf[4096];
	unsigned char destBuf[4096];
	unsigned char *sPointer;
	unsigned char *dPointer;
	enum engine_status eng_st;
	struct req_progress p;
	/**status*/
	int ID;
	int firstFlag;
	int IFlag;
	int totalRequestSize;
	int Qstart;	
	int stopOfQ;
	int stopOfI;
//	int terminate;
	/*counters*/
	int numOfTask;
	int counter;
//	int currentOrder;
	spinlock_t lockOfIFlag;//IFlag
};

static struct crypto_priv *cpg[10];

struct common_struct {
	/* the lock protects queue and eng_st */
//	spinlock_t lockOfQ;
	spinlock_t lockOfH;//queue
//	spinlock_t lockOfReadI;
//	spinlock_t lockOfOrder;
	struct crypto_queue queue;//com own the queue	
	struct crypto_async_request **taskPointer_Q;
	struct crypto_async_request **taskPointer_I;
	int exitFlag;
//	long totalNumOfRequest;
//	long totalNumOfMapping;
};
static struct common_struct *com;

struct mv_ctx {
	u8 aes_enc_key[AES_KEY_LEN * 2];
	u32 aes_dec_key[8];
	int key_len;
	u32 need_calc_aes_dkey;
};

enum crypto_op {
	COP_AES_ECB
};

struct mv_req_ctx {
	enum crypto_op op;
	int decrypt;
};

/* Write a 256 bit field (either a writable key or IV) */
static inline void
_writefield(u32 offset, void *value)
{
	int i;
	for (i = 0; i < 8; i++)
		iowrite32(cpu_to_be32(((u32 *)value)[i]), dsi_aes_dma.map + offset + (i * 4));
}

/* Read a 128 bit field (either a writable key or IV) */
static inline void
_readfield(u32 offset, void *value)
{
	int i;
	for (i = 0; i < 4; i++)
		((u32 *) value)[i] = ioread32(dsi_aes_dma.map + offset + (i * 4));
}

void dma_wr_reg(u32 offset, u32 val)
{
	// ToDo: Handle endianness if required.  Intel/Linux = Little Endian
	iowrite32(val, dsi_aes_dma.map +  offset);
}

u32 dma_rd_reg(u32 offset)
{
	// ToDo: Handle endianness if required.  Intel/Linux = Little Endian
	return ioread32(dsi_aes_dma.map + offset);
}

static int flag = 0;
static inline void dequeue_complete_req(struct crypto_priv *localCpg,
			struct crypto_async_request **local_taskPointer);
static inline void DataPrepare(struct crypto_priv *localCpg,
			struct crypto_async_request **local_taskPointer);
static int do_crypt(void *src, void *dst, int len, u32 flags);//one char by char

int crypto_aes_expand_key_generic(struct crypto_aes_ctx *ctx, const u8 *in_key,
		unsigned int key_len);
int crypto_aes_set_key_generic(const u8 *in_key,
		unsigned int key_len);
void aes_encrypt_generic(u8 *out, const u8 *in);
void aes_decrypt_generic(u8 *out, const u8 *in);

struct timespec start, end;
//struct timespec switch_start, switch_end;
static DECLARE_WAIT_QUEUE_HEAD(wq);
static DECLARE_WAIT_QUEUE_HEAD(wq0);

//static DECLARE_WAIT_QUEUE_HEAD(wqi);
static DEFINE_MUTEX(Isem);
static DEFINE_MUTEX(Qsem);
/*spearte extract part and dequeue_complete part will not allow huge data block
*/
static int interrupt_manag(struct crypto_priv *localCpg)
{	
	int numOfRun_I=0;
	int dataSize=0;
	int id=localCpg->ID;
	int numOfTask_I;
	do{	
		if(localCpg->numOfTask==0)
			goto Ifinish;
Iacquire:
		/*GO*/
		__set_current_state(TASK_UNINTERRUPTIBLE);
		//printk(KERN_INFO "before I%d dataprepare, high layer shouldn't call!",id);
		DataPrepare(localCpg,localCpg->request_collector);
		//printk(KERN_INFO "after I%d dataprepare,",id);
		mutex_lock(&Isem);
		if (localCpg->firstFlag)
			do_crypt(localCpg->sourceBuf, localCpg->destBuf, localCpg->totalRequestSize, AES_DIR_DEC | RDMATLPS_START_OP);
		else
			do_crypt(localCpg->sourceBuf, localCpg->destBuf, localCpg->totalRequestSize, AES_DIR_ENC | RDMATLPS_START_OP);
		mutex_unlock(&Isem);
		localCpg->totalRequestSize=0;
		localCpg->eng_st = ENGINE_W_DEQUEUE;//now it's turn for Q to do dequeue
		wake_up_all(&wq);
Ifinish:		
		wait_event_interruptible(wq,localCpg->IFlag||com->exitFlag);
		spin_lock_irq(&localCpg->lockOfIFlag);
		localCpg->IFlag=0;
		spin_unlock_irq(&localCpg->lockOfIFlag);	
		if(com->exitFlag)
			goto iexit;
		goto Iacquire;	
	} while (!kthread_should_stop());
iexit:	
	printk(KERN_INFO "Exiting interrupt Manager.");
	return 0;
}

static int queue_manag(struct crypto_priv *localCpg)
{
	struct crypto_async_request *async_req = NULL;
	struct crypto_async_request *backlog = NULL;
	struct crypto_queue *queue=&com->queue;
	struct ablkcipher_request *req= NULL;
	struct mv_req_ctx *req_ctx=NULL;
	struct crypto_async_request **cPointer;//collector pointer point to the array of pointer
	int forceProcess=0;
	// int maxData=4096;//assuming each request have 512 bytes data
	int maxData=512*7;//assuming each request have 512 bytes data
	int id=localCpg->ID;//0 or 1
	localCpg->eng_st = ENGINE_IDLE;
	cPointer=localCpg->request_collector;
	localCpg->Qstart=1;
	do {	
qdequeue:
		/*dequeue_complete*/
		__set_current_state(TASK_UNINTERRUPTIBLE);
		if(localCpg->eng_st == ENGINE_W_DEQUEUE){
		//printk(KERN_INFO "before Q%d dequeue_comp, high layer shouldn't call! untile see after dequeue",id);
			dequeue_complete_req(localCpg,localCpg->request_collector);
		//printk(KERN_INFO "after Q%d dequeue_comp",id);
			localCpg->eng_st=ENGINE_IDLE;
			if(!id&&queue->qlen<8) goto qwait;
		}
qacquire:		 	
		__set_current_state(TASK_UNINTERRUPTIBLE);
		mutex_lock(&Qsem);
		/*collect*/
		//printk(KERN_INFO "before Q%d collect, high layer shouldn't call until see after collect!",id);
		if (localCpg->eng_st == ENGINE_IDLE) {		
qcollect:
			spin_lock_irq(&com->lockOfH);
			backlog = crypto_get_backlog(&com->queue);
			async_req = crypto_dequeue_request(&com->queue);
			spin_unlock_irq(&com->lockOfH);			
			if (async_req) {			
				req= ablkcipher_request_cast(async_req);	
				req_ctx= ablkcipher_request_ctx(req);	
				*cPointer=async_req; /*address in async_req copied into request_collector */	
				cPointer++;
				localCpg->totalRequestSize += req->nbytes;
				localCpg->numOfTask++;
				if(localCpg->numOfTask==1) {
					localCpg->firstFlag = req_ctx->decrypt;
				}
				if(localCpg->totalRequestSize >= maxData || req_ctx->decrypt != localCpg->firstFlag) {
					forceProcess=1;
				}
			} else { //no more request
				if(localCpg->numOfTask>0) {
					forceProcess=1;
				}
			}
		}

		if (backlog) {
			backlog->complete(backlog, -EINPROGRESS);
			backlog = NULL;
		}

		if(forceProcess)
		{			
			forceProcess=0;
			localCpg->eng_st = ENGINE_BUSY;	
			spin_lock_irq(&localCpg->lockOfIFlag);			
			localCpg->IFlag=1;
			spin_unlock_irq(&localCpg->lockOfIFlag);
			cPointer = localCpg->request_collector;	
			goto qrelease;
		} else if(localCpg->eng_st==ENGINE_IDLE) {	
				goto tcheck;
		}
qrelease:
			/*release*/
		mutex_unlock(&Qsem);
		wake_up_all(&wq);
		//printk(KERN_INFO "after Q%d collect",id);
		wait_event_interruptible(wq,localCpg->eng_st == ENGINE_W_DEQUEUE||com->exitFlag);
		if(com->exitFlag)
			goto qexit;
		goto qdequeue;
tcheck:
		if(!queue->qlen&&!localCpg->numOfTask) {	
			/*release*/
			mutex_unlock(&Qsem);
			wake_up_all(&wq);
qwait:	
			if(!id) //Q0 is prepare for every single request
				wait_event_interruptible(wq0,queue->qlen!=0||com->exitFlag);
			else 		
				//wait_event_interruptible(wq,((queue->qlen!=0&&cpg[0]->firstFlag!=1)||com->exitFlag));			
				wait_event_interruptible(wq,queue->qlen!=0||com->exitFlag);			
			if(com->exitFlag)
				goto qexit;
			cPointer = localCpg->request_collector;
			goto qacquire;
		}else{
			goto qcollect;
		}
	} while (!kthread_should_stop());
qexit:
	if(com->exitFlag)
	printk(KERN_INFO "rmmod being called Q%d exit \n.",id);	
	return 0;
}

static int
do_crypt(void *src, void *dst, int len, u32 flags)
{
	u32 status;
	u32 counter = 50000;
	int iLenCtr, old_len;
	long nSec;
	unsigned long iflags;
	struct timespec tsBefore, tsAfter;
	struct crypto_queue *queue=&com->queue;

	//spin_lock_irqsave(&lock, iflags);	
	if (key_size == AES_KEYSIZE_256) {
		// printk(KERN_WARNING "do crypt: start hardware encrypt/decrypt; flags = %08x; len = %d", flags, len);
	
		// printk(KERN_WARNING "do crypt: start encrypt/decrypt; flags = %08x; len = %d", flags, len);
		/* copy the source buffer to our DMA memory */
		// printk(KERN_WARNING "do crypt: copying src to rd_buf");
		memcpy(rd_buf, src, len);
		// DMEM32(rd_buf, len);

		/* set the length, operation (encrypt/decrypt), and start bits */
		// printk(KERN_WARNING "do crypt: writing %08x to RDMATLPS", (unsigned int)(len | flags));
		// getnstimeofday(&tsBefore);
		dma_wr_reg(RDMATLPS, len | flags); // caveat: make sure flags contain direction & start bits

	//	do {
	//	 	status = dma_rd_reg(DCSR);
			// cpu_relax();
			// ndelay(10);
	//	} while (!(status & DCSR_WRITE_DONE) && --counter);
		//printk(KERN_INFO "start to wait, queue size is %d",queue->qlen);
		int ret;
WH:
//		getnstimeofday(&start);
		if (flags & AES_DIR_DEC) 
		ret=wait_event_interruptible_timeout(wq, (dma_rd_reg(DCSR) & DCSR_WRITE_DONE), 3);
		else
		ret=wait_event_interruptible_timeout(wq, (dma_rd_reg(DCSR) & DCSR_WRITE_DONE), 3);
		 if(!ret)
		 {
//			getnstimeofday(&end);
//			long difference = end.tv_nsec - start.tv_nsec;
//			printk("\n 2 jiffy is %ld\n", difference);
			printk(KERN_INFO "!!!!!!!!!!!!!!!!shouldn't be show!");
			goto WH;
		 }

		//printk(KERN_INFO "after  wait, queue size is %d",queue->qlen);
		// printk(KERN_WARNING "do crypt: got the following status %08x; counter %d", status, counter);
		// } while (((status & 0x0f) != (DSCR_WRITE_DONE | DCSR_READ_DONE)) && --counter); 
		// we should note that we are only looking for write (dma writes to system memory) done status
	
		/* copy the DMA result buffer to destination buffer */
		// printk(KERN_WARNING "do crypt: copying wr_buf to dst");
		// getnstimeofday(&tsAfter);
		memcpy(dst, wr_buf, len);
		// DMEM32(wr_buf, len);
		// nSec = tsAfter.tv_nsec - tsBefore.tv_nsec;
		// printk(KERN_WARNING "do crypt: performance for %d bytes is %ld ns. After %d loops.", len, nSec, counter);

		/* Clear the event */
		//spin_unlock_irqrestore(&lock, iflags);
		return counter ? 0 : 1;
	
 	} else {
		u8 *src_walk = (u8 *)src;
		u8 *dst_walk = (u8 *)dst;
		printk(KERN_WARNING "do crypt: start software encrypt/decrypt; flags = %08x; len = %d", flags, len);
		// printk(KERN_WARNING "do crypt: printing source buffer");
		// DMEM32(src, len);
		old_len = len;
		do {
			// printk(KERN_WARNING "do_crypt: looping through plaintext/ciphertext (%d).", len);

			if (flags & AES_DIR_DEC) {
				// printk(KERN_WARNING "do_crypt: DECRYPTING");
				aes_decrypt_generic(dst_walk, src_walk);
			} else {
				// printk(KERN_WARNING "do_crypt: ENCRYPTING");
				aes_encrypt_generic(dst_walk, src_walk);
			}
			len -= AES_MIN_BLOCK_SIZE;
			src_walk += AES_MIN_BLOCK_SIZE;
			dst_walk += AES_MIN_BLOCK_SIZE;
		} while (len);
		// printk(KERN_WARNING "do crypt: printing destination buffer");
		// DMEM32(dst, old_len);
		//spin_unlock_irqrestore(&lock, iflags);	
#if 0
		if(memcmp(dst, testbuf, old_len) != 0) {
			int i;
			static int firstTimeFlag = 0;
			u8 *dst_ptr = (u8 *)dst;
			printk(KERN_WARNING "do crypt: the software and hardware encryption output are different!!!");
			if (firstTimeFlag == 0) {
				printk(KERN_WARNING "printing source data");
				DMEM32(src, old_len);
				printk(KERN_WARNING "printing output difference (data = hw:sw)");
				for (i = 0; i < old_len; i++) {
					if (dst_ptr[i] != testbuf[i])
						printk(KERN_WARNING "at index %d, data: %02x:%02x", i, dst_ptr[i], testbuf[i]);
				}
			}
			firstTimeFlag = 1;
		} else {
			printk(KERN_WARNING "do crypt: the software and hardware encryption output are the same!");
		}
#endif
		return 0;
	}
}

#if 0
static inline void do_crypt(void *src, void *dst, int len, u32 flags)
{
	u8 *src_walk = (u8 *)src;
	u8 *dst_walk = (u8 *)dst;
	do {
		if (!flags)
			aes_encrypt_generic(dst_walk, src_walk);
		else
			aes_decrypt_generic(dst_walk, src_walk);
		len -= AES_MIN_BLOCK_SIZE;
		src_walk += AES_MIN_BLOCK_SIZE;
		dst_walk += AES_MIN_BLOCK_SIZE;
	} while (len);
}
#endif

static inline int count_sgs(struct scatterlist *sl, unsigned int total_bytes)
{
	int i = 0;
	size_t cur_len;

	while (sl) {
		cur_len = sl[i].length;
		++i;
		if (total_bytes > cur_len)
			total_bytes -= cur_len;
		else
			break;
	}

	return i;
}
static int mv_handle_req(struct crypto_async_request *req)
{
	unsigned long flags;
	int ret;
	struct crypto_queue *queue=&com->queue;
	spin_lock_irqsave(&com->lockOfH, flags);
	ret = crypto_enqueue_request(&com->queue, req);
	spin_unlock_irqrestore(&com->lockOfH, flags);
	//printk(KERN_INFO "!!!!!!enqueue being called, queue size is %d \n",queue->qlen);
	//printk(KERN_INFO "S0 is %d,S1 is %d,Is0 is %d, Is1 is %d",cpg[0]->stopOfQ,cpg[1]->stopOfQ,cpg[0]->stopOfI,cpg[1]->stopOfI);
//	if(cpg[0]->stopOfQ&&cpg[1]->stopOfQ&&cpg[0]->stopOfI&&cpg[1]->stopOfI)
//	{
		if(!list_empty(&wq0.task_list))
		wake_up_all(&wq0);
		if(queue->qlen>8)
		wake_up_all(&wq);
		//printk(KERN_INFO "high layer wake up all,queue size is %d",queue->qlen);
//	}
	return ret;
}
static int mv_enc_aes_ecb(struct ablkcipher_request *req)
{
	int flags;
	struct mv_req_ctx *req_ctx = ablkcipher_request_ctx(req);
	req_ctx->op = COP_AES_ECB;
	req_ctx->decrypt = 0;
	return mv_handle_req(&req->base);
}
static inline void compute_aes_dec_key(struct mv_ctx *ctx)
{
	struct crypto_aes_ctx gen_aes_key;
	int key_pos;

	if (!ctx->need_calc_aes_dkey)
		return;

	crypto_aes_expand_key_generic(&gen_aes_key, ctx->aes_enc_key, ctx->key_len);

	key_pos = ctx->key_len + 24;
	memcpy(ctx->aes_dec_key, &gen_aes_key.key_enc[key_pos], 4 * 4);
	switch (ctx->key_len) {
	case AES_KEYSIZE_256:
		key_pos -= 2;
		/* fall */
	case AES_KEYSIZE_192:
		key_pos -= 2;
		memcpy(&ctx->aes_dec_key[4], &gen_aes_key.key_enc[key_pos],
				4 * 4);
		break;
	}
	ctx->need_calc_aes_dkey = 0;
	//printk(KERN_INFO "%s: setting key, len = %d.\n",__func__, ctx->key_len);
	//DMEM32(ctx->aes_dec_key, ctx->key_len);
#if 0
	if (ctx->key_len == AES_KEYSIZE_256) {
	 	printk(KERN_INFO "compute_aes_dec_key: inside len = aes_keysize_256 condition");
		// _writefield(AESKEY0_0, ctx->aes_dec_key); // we can only support 256 bits now
		dma_wr_reg(AESKEY0_0, ctx->aes_dec_key[0]);
		dma_wr_reg(AESKEY0_0 + 4, ctx->aes_dec_key[1]);
		dma_wr_reg(AESKEY0_0 + 8, ctx->aes_dec_key[2]);
		dma_wr_reg(AESKEY0_0 + 12, ctx->aes_dec_key[3]);
		dma_wr_reg(AESKEY0_0 + 16, ctx->aes_dec_key[4]);
		dma_wr_reg(AESKEY0_0 + 20, ctx->aes_dec_key[5]);
		dma_wr_reg(AESKEY0_0 + 24, ctx->aes_dec_key[6]);
		dma_wr_reg(AESKEY0_0 + 28, ctx->aes_dec_key[7]);
		return 0;
	}


#endif

}
static int mv_dec_aes_ecb(struct ablkcipher_request *req)
{
	int flags;
	struct mv_ctx *ctx = crypto_tfm_ctx(req->base.tfm);
	struct mv_req_ctx *req_ctx = ablkcipher_request_ctx(req);
	struct crypto_queue *queue=&com->queue;
	// printk(KERN_INFO "dec aes ecb method being called");
	req_ctx->op = COP_AES_ECB;
	req_ctx->decrypt = 1;
	compute_aes_dec_key(ctx);
	// printk(KERN_INFO "dec aes ecb method being alled:The size of queue is %d",queue->qlen);
	return mv_handle_req(&req->base);
}
static inline void mv_crypto_algo_completion(int id)
{
	sg_miter_stop(&cpg[id]->p.src_sg_it);
	sg_miter_stop(&cpg[id]->p.dst_sg_it);
}
static inline void DataPrepare(struct crypto_priv *localCpg,
			struct crypto_async_request **local_taskPointer)	
{
	struct req_progress *p = &localCpg->p;
	struct ablkcipher_request *req;
	int num_sgs;
	int ret;
	void *sbuf;
	int copy_len;
	int len;
	char *dbuf;
	localCpg->sPointer=localCpg->sourceBuf;
	memset(p, 0, sizeof(struct req_progress));//initial p to 0
	p->complete = mv_crypto_algo_completion;//static void mv_crypto_algo_completion(int)
	//p->process = mv_process_current_q;
	while(localCpg->numOfTask>0)
	{
	//	//printk(KERN_INFO "in dataPrepare crypto_async_request %p", *local_taskPointer);	
		req =ablkcipher_request_cast(*local_taskPointer);
		local_taskPointer++;
	//	//printk(KERN_INFO "in dataPrepare ablkcipher_request %p", req);	
		p->hw_nbytes = req->nbytes;//
		num_sgs = count_sgs(req->src, req->nbytes);
	//	//printk(KERN_INFO "req->nbytes is %d",req->nbytes);
		sg_miter_start(&p->src_sg_it, req->src, num_sgs, SG_MITER_FROM_SG);
	//	//printk(KERN_WARNING "entering copy_src_to_buf");
		dbuf=localCpg->sPointer;
		len=p->hw_nbytes;
		while (len) 
		{
			if (!p->sg_src_left) 
			{
				ret = sg_miter_next(&p->src_sg_it);
				BUG_ON(!ret);
				p->sg_src_left = p->src_sg_it.length;
				p->src_start = 0;
			}
				sbuf = p->src_sg_it.addr + p->src_start;
				copy_len = min(p->sg_src_left, len);
				memcpy(dbuf, sbuf, copy_len);
				p->src_start += copy_len;
				p->sg_src_left -= copy_len;
				len -= copy_len;
				dbuf += copy_len;
		} 
		localCpg->sPointer += p->hw_nbytes;
		localCpg->counter++;
		localCpg->numOfTask--;
		//printk(KERN_DEBUG "I%d is in data prepare,numOfTask is %d",localCpg->ID,localCpg->numOfTask);
	}
	//printk(KERN_INFO "Exit data prepare method: total data size is %d ",localCpg->totalRequestSize);
}

static inline void dequeue_complete_req(struct crypto_priv *localCpg,
			struct crypto_async_request **local_taskPointer)	
{
	struct ablkcipher_request *req; 
	struct crypto_async_request *asreq;
	struct req_progress *p = &localCpg->p;
	int num_sgs;
	int ret;
	int offset;
	int dst_copy;
	void *buf;	
	int len;
	char *sbuf;
	localCpg->dPointer=localCpg->destBuf;
	while(localCpg->counter> 0) {
		req =ablkcipher_request_cast(*local_taskPointer);
		asreq=*local_taskPointer;
		local_taskPointer++;
		p->hw_nbytes = req->nbytes;//
		num_sgs = count_sgs(req->dst, req->nbytes);
		sg_miter_start(&p->dst_sg_it, req->dst, num_sgs, SG_MITER_TO_SG);	
		
		offset = 0;	
		sbuf=localCpg->dPointer;
		len=p->hw_nbytes;	
		do {
			if (!localCpg->p.sg_dst_left) {
				ret = sg_miter_next(&localCpg->p.dst_sg_it);
				BUG_ON(!ret);
				localCpg->p.sg_dst_left = localCpg->p.dst_sg_it.length;
				localCpg->p.dst_start = 0;
			}
			buf = localCpg->p.dst_sg_it.addr;
			buf += localCpg->p.dst_start;
			dst_copy = min(len, localCpg->p.sg_dst_left);
			memcpy(buf,
			       sbuf + offset,
			       dst_copy);
			offset += dst_copy;
			localCpg->p.sg_dst_left -= dst_copy;
			len -= dst_copy;
			localCpg->p.dst_start += dst_copy;
		} while (len > 0);
		localCpg->counter--;
		localCpg->dPointer+= p->hw_nbytes;
//		spin_lock_irq(&com->lockOfOrder);
//		com->totalNumOfMapping++;
//		spin_unlock_irq(&com->lockOfOrder);
		local_bh_disable();
		asreq->complete(asreq, 0);
		local_bh_enable();				
		localCpg->p.complete(localCpg->ID);
	}	
}
static int mv_cra_init(struct crypto_tfm *tfm)
{
	tfm->crt_ablkcipher.reqsize = sizeof(struct mv_req_ctx);
	return 0;
}
/* CRYPTO-API Functions */
//notes, the API function input paramater has small difference with dsi aes
static int mv_setkey_aes(struct crypto_ablkcipher *cipher, const u8 *key,
		unsigned int len)
{
	struct crypto_tfm *tfm = crypto_ablkcipher_tfm(cipher);
	struct mv_ctx *ctx = crypto_tfm_ctx(tfm);
	unsigned int ret;

	key_size = ctx->key_len = len;
	ctx->need_calc_aes_dkey = 0;
	//printk(KERN_WARNING "dsi_setkey_blk: setting key, len = %d.", len);

//	printk(KERN_INFO "%s: setting key before set key generic, len = %d.", __func__, len);
	//DMEM32(key, len);
	crypto_aes_set_key_generic(key, len);
//	printk(KERN_INFO "%s: setting key after set key generic, len = %d.", __func__, len);
	//DMEM32(key, len);

//	//printk(KERN_INFO "crypto set key being called");
	memcpy(ctx->aes_enc_key, key, len);
	
	if (len == AES_KEYSIZE_256) {
		mutex_lock(&Isem);
//	 	printk(KERN_INFO "dsi_setkey_blk: inside len = aes_keysize_256 condition");
		_writefield(AESKEY0_0, key); // we can only support 256 bits now
		mutex_unlock(&Isem);
		return 0;
	}

	return 0;
}

struct crypto_alg mv_aes_alg_ecb = {
	.cra_name		= "ecb(aes)",
	.cra_driver_name	= "mv-ecb-aes",
	.cra_priority	= 300,
	.cra_flags	= CRYPTO_ALG_TYPE_ABLKCIPHER | CRYPTO_ALG_ASYNC,
	.cra_blocksize	= 16,
	.cra_ctxsize	= sizeof(struct mv_ctx),
	.cra_alignmask	= 0,
	.cra_type	= &crypto_ablkcipher_type,
	.cra_module	= THIS_MODULE,
	.cra_init	= mv_cra_init,
	.cra_u		= {
		.ablkcipher = {
			.min_keysize	=	AES_MIN_KEY_SIZE,
			.max_keysize	=	AES_MAX_KEY_SIZE,
			.setkey		=	mv_setkey_aes,
			.encrypt	=	mv_enc_aes_ecb,
			.decrypt	=	mv_dec_aes_ecb,
		},
	},
};


#if 0
static int __devinit
dsi_aes_probe(struct pci_dev *dev, const struct pci_device_id *id)
{
}

static void __devexit dsi_aes_remove(struct pci_dev *dev)
{
	crypto_unregister_alg(&mv_aes_alg_ecb);
	if (stat_flags & HAVE_REGION)
		release_mem_region(dsi_aes_dma.addr, DMA_REGISTER_SIZE);
	iounmap(dsi_aes_dma.map);
	dsi_aes_dma.map = NULL;

	pci_release_regions(dev);
	pci_disable_device(dev);
}


static int __init dsi_crypto_init(void)
{
	//return pci_register_driver(&dsi_aes_driver);
int ret;

#ifdef DSI_AES_ECB_ENABLE
        //printk(KERN_WARNING "dsi-aes: registering dsi_ecb_alg.\n");
        ret = crypto_register_alg(&mv_aes_alg_ecb);
        if (ret)
                goto ealg;
#endif
        //printk(KERN_WARNING "dsi-aes: DSI AES engine enabled.\n");
		com = kzalloc(sizeof(struct common_struct), GFP_KERNEL);
		if (!com)
			return -ENOMEM;
		com->exitFlag=0;
		spin_lock_init(&com->lockOfH);
//		spin_lock_init(&com->lockOfReadI);
		//spin_lock_init(&com->lockOfacquireI);
		//spin_lock_init(&com->lockOfacquireQ);
		crypto_init_queue(&com->queue,50);
		//printk(KERN_WARNING "queue initialized\n");	
		
		
		int i;
		for(i=0;i<numOfCpg;i++){	
			cpg[i] = kzalloc(sizeof(struct crypto_priv), GFP_KERNEL);
			if (!cpg[i])
				return -ENOMEM;
			spin_lock_init(&cpg[i]->lockOfIFlag);
			cpg[i]->ID=i;
			cpg[i]->queue_th = kthread_run(queue_manag, cpg[i], "mv_crypto");
			cpg[i]->interrupt_th = kthread_run(interrupt_manag, cpg[i], "mv_crypto");
		}
		return 0;
		
 eecb:
#ifdef DSI_AES_ECB_ENABLE
        crypto_unregister_alg(&mv_aes_alg_ecb);
#endif
 ealg:
#ifdef DSI_AES_ALG_ENABLE
       // crypto_unregister_alg(&dsi_alg);
#endif
 eexit:
        printk(KERN_WARNING "dsi-aes: DSI AES loading failed.\n");
}
module_init(dsi_crypto_init);

static void __exit dsi_crypto_exit(void)
{
	//pci_unregister_driver(&dsi_aes_driver);
#ifdef DSI_AES_ECB_ENABLE
        crypto_unregister_alg(&mv_aes_alg_ecb);
        //printk(KERN_WARNING "dsi-aes: DSI AES engine disabled.\n");
#endif
		com->exitFlag=1;
		wake_up_all(&wq);
		int i;
		for(i=0;i<numOfCpg;i++){
			kthread_stop(cpg[i]->queue_th);
			kthread_stop(cpg[i]->interrupt_th);
		}
}

module_exit(dsi_crypto_exit);
#endif

static void __devexit
dsi_aes_remove(struct pci_dev *dev)
{

	crypto_unregister_alg(&mv_aes_alg_ecb);

	com->exitFlag=1;
	wake_up_all(&wq);
	int i;
	for(i=0;i<numOfCpg;i++){
		kthread_stop(cpg[i]->queue_th);
		kthread_stop(cpg[i]->interrupt_th);
	}

	if (stat_flags & HAVE_REGION)
		release_mem_region(dsi_aes_dma.addr, DMA_REGISTER_SIZE);
	pci_free_consistent(dev, BUF_SIZE, rd_buf, rd_hw_addr);
	pci_free_consistent(dev, BUF_SIZE, wr_buf, wr_hw_addr);
	rd_buf = wr_buf = NULL;

	iounmap(dsi_aes_dma.map);
	dsi_aes_dma.map = NULL;

	pci_release_regions(dev);
	pci_disable_device(dev);
}

static int __devinit
dsi_aes_probe(struct pci_dev *dev, const struct pci_device_id *id)
{
	int ret;
	ret = pci_enable_device(dev);
	if (ret) {
		printk(KERN_WARNING "%s: cannot enable device.\n", __func__); 
		return ret;
	}

	ret = pci_request_regions(dev, "dsi-aes");
	if (ret) {
		printk(KERN_WARNING "%s: cannot get memory region.\n", __func__); 
		goto eenable;
	}

	/* Initialize the FPGA/DMA memory */
	dsi_aes_dma.addr = pci_resource_start(dev, 0);
	dsi_aes_dma.size = pci_resource_len(dev, 0);
	dsi_aes_dma.map = ioremap(dsi_aes_dma.addr, dsi_aes_dma.size);	
	if (!dsi_aes_dma.map) {
		printk(KERN_WARNING "%s: cannot get virtual address.\n", __func__);
		goto erequest;
	}
	printk(KERN_INFO "%s: Base HW Addr: %X; Virtual HW Addr: %X\n", __func__, dsi_aes_dma.addr, (unsigned int)dsi_aes_dma.map);	
	
	spin_lock_init(&lock);

#if 0
	/* Check memory region to see if it is in use */
	if (check_mem_region(dsi_aes_dma.addr, DMA_REGISTER_SIZE) < 0) {
		printk(KERN_WARNING "%s: memory in use.\n", __func__);
		goto eiomap;
	}
#endif
 
	/* Try to gain exclusive control of memory */
	request_mem_region(dsi_aes_dma.addr, DMA_REGISTER_SIZE, "dsi-aes");
	stat_flags = stat_flags | HAVE_REGION; 	
	printk(KERN_INFO "%s: hardware initialization done.\n", __func__);

	/* Allocate read & write buffers */
	rd_buf = pci_alloc_consistent(dev, BUF_SIZE, &rd_hw_addr);
	if (!rd_buf) {
		printk(KERN_CRIT "%s: unable to allocate read buffer.\n", __func__);
		goto ememrel;
	}	
	printk(KERN_INFO "%s: read buffer allocation: %08x->%08x\n", __func__, rd_hw_addr, rd_buf);
 
	wr_buf = pci_alloc_consistent(dev, BUF_SIZE, &wr_hw_addr);
	if (!wr_buf) {
		printk(KERN_CRIT "%s: unable to allocate write buffer.\n", __func__);
		goto erdmemrel;
	}	
	printk(KERN_INFO "%s: write buffer allocation: %08x->%08x\n", __func__, wr_hw_addr, wr_buf);

	/* set the start address of FPGA read */
	dma_wr_reg(RDMATLPSA, rd_hw_addr);	
	printk(KERN_INFO "set the start address of FPGA read done\n");
	
	/* set the start address of FPGA write */
	dma_wr_reg(WDMATLPDA, wr_hw_addr);	
	printk(KERN_INFO "set the start address of FPGA write done\n");


	ret = crypto_register_alg(&mv_aes_alg_ecb);
	if (ret)
		goto ewrmemrel;

        //printk(KERN_WARNING "dsi-aes: DSI AES engine enabled.\n");
	com = kzalloc(sizeof(struct common_struct), GFP_KERNEL);
	if (!com)
		return -ENOMEM;
	com->exitFlag=0;
	spin_lock_init(&com->lockOfH);
//	spin_lock_init(&com->lockOfReadI);
	//spin_lock_init(&com->lockOfacquireI);
	//spin_lock_init(&com->lockOfacquireQ);
	crypto_init_queue(&com->queue,50);
	//printk(KERN_WARNING "queue initialized\n");	
		
	int i;
	for(i=0;i<numOfCpg;i++){	
		cpg[i] = kzalloc(sizeof(struct crypto_priv), GFP_KERNEL);
		if (!cpg[i])
			return -ENOMEM;
		spin_lock_init(&cpg[i]->lockOfIFlag);
		cpg[i]->ID=i;
		cpg[i]->queue_th = kthread_run(queue_manag, cpg[i], "mv_crypto");
		cpg[i]->interrupt_th = kthread_run(interrupt_manag, cpg[i], "mv_crypto");
	}

	printk(KERN_WARNING "dsi-aes: DSI AES engine enabled.\n");
	return 0;

 ewrmemrel:
	pci_free_consistent(dev, BUF_SIZE, wr_buf, wr_hw_addr);	

 erdmemrel:
	pci_free_consistent(dev, BUF_SIZE, rd_buf, rd_hw_addr);	

 ememrel:
	release_mem_region(dsi_aes_dma.addr, DMA_REGISTER_SIZE);

 eiomap:
	pci_iounmap(dev, dsi_aes_dma.map);

 erequest:
	pci_release_regions(dev);

 eenable:
	pci_disable_device(dev);

	printk(KERN_ERR "dsi-aes: DSI AES initialization failed.\n");
	return ret;
}

static struct pci_device_id 
dsi_aes_tbl[] = 
{
	{
		.vendor	=	DSI_HW_CRYPT_VENDOR_ID,
		.device	=	DSI_HW_CRYPT_DEVICE_ID,
		.subvendor =	DSI_HW_CRYPT_SUBVENDOR_ID,
		.subdevice =	DSI_HW_CRYPT_SUBDEVICE_ID,
	},
	{0, }
};
MODULE_DEVICE_TABLE(pci, dsi_aes_tbl);

static struct pci_driver dsi_aes_driver = {
	.name = "DSI AES Driver",
	.id_table = dsi_aes_tbl,
	.probe = dsi_aes_probe,
	.remove = __devexit_p(dsi_aes_remove)
};

static int __init
dsi_crypto_init(void)
{
	return pci_register_driver(&dsi_aes_driver);
}

static void __exit
dsi_crypto_exit(void)
{
	pci_unregister_driver(&dsi_aes_driver);
}

MODULE_AUTHOR("Data Center Technologies - Data Storage Institute");
MODULE_DESCRIPTION("DSI hardware AES driver");
MODULE_LICENSE("GPL");
MODULE_ALIAS("platform:mv_crypto");

module_init(dsi_crypto_init);
module_exit(dsi_crypto_exit);
