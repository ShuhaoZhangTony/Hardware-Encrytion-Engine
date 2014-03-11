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
#define MV_CESA	"MV-CESA:"
#define MAX_HW_HASH_SIZE	0xFFFF
#define DMA_REGISTER_SIZE         (4 * DREGCOUNT)    // There are eighteen registers, and each is 4 bytes wide.



//#define DSI_DMA_ENABLE
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
#define numOfCpg 5
/* Static structures */
enum {
	DSCR,		 //Device control/status register 
	DDMACR,		 //DMA control register 
	WDMATLPA,	 //address of destination data buffer (device perspective)
	WDMATLPS,
	WDMATLPC,
	WDMATLPP,
	RDMATLPP,
	RDMATLPA,	 //address of source data buffer (device perspective) 
	RDMATLPS,
	RDMATLPC,
	WDMAPERF,
	RDMAPERF,
	RDMASTAT,
	NRDCOMP,
	RCOMPDSIZW,
	DLWSTAT,
	DLTRSSTAT,
	DMISCCONT,
	
	AESLENCR,	 //AES length & control register; BIT31 1=encrypt, 0=decrypt; BIT0-15 number of bytes to encrypt 
	AESKEY0_0,	 //AES key MSW 
	AESKEY0_1,
	AESKEY0_2,
	AESKEY0_3,	 //AES key LSW 

	DREGCOUNT
};
typedef struct
dma_mem_struct
{
	unsigned long addr;
	unsigned long size;
	void __iomem  *map;
}	dma_mem_t;
static dma_mem_t dsi_aes_dma;
static unsigned long stat_flags = 0;
static unsigned char *wr_buf = NULL, *rd_buf = NULL, *unaligned_buf = NULL;
static dma_addr_t rd_hw_addr, wr_hw_addr;
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
	//I am assume the hardware will finish hw_nbytes everytime 
	//instead of finish it in multiple cycle.
	// which is a wrong assumtion.
};

struct crypto_priv {
	/**critical members*/
	struct crypto_async_request *request_collector[10];//this array is used to store address of request
	struct task_struct *queue_th;
	struct task_struct *interrupt_th;
	unsigned char sourceBuf[BUF_SIZE];
	unsigned char destBuf[BUF_SIZE];
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
	struct mutex mutexOfReg;
};

static struct crypto_priv *cpg[numOfCpg];

struct common_struct {
	/* the lock protects queue and eng_st */
//	spinlock_t lockOfQ;
	spinlock_t lockOfH;//queue
	spinlock_t lockOfIFlag;//IFlag
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
	u8 aes_enc_key[AES_KEY_LEN];
	u32 aes_dec_key[8];
	int key_len;
	u32 need_calc_aes_dkey;
};

enum crypto_op {
	COP_AES_ECB,
	//COP_AES_CBC,
};

struct mv_req_ctx {
	enum crypto_op op;
	int decrypt;
};
static inline void
_writefield(u32 offset, void *value)
{
#if 1 
	int i;
	for (i = 0; i < 4; i++)
		iowrite32(((u32 *) value)[i], dsi_aes_dma.map + offset + (i * 4));
#endif
}

/* Read a 128 bit field (either a writable key or IV) */
static inline void
_readfield(u32 offset, void *value)
{
#if 1
	int i;
	for (i = 0; i < 4; i++)
		((u32 *) value)[i] = ioread32(dsi_aes_dma.map + offset + (i * 4));
#endif
}

static int flag = 0;
static inline void dequeue_complete_req(struct crypto_priv *localCpg,
			struct crypto_async_request **local_taskPointer);
static inline void DataPrepare(struct crypto_priv *localCpg,
			struct crypto_async_request **local_taskPointer);
static void do_crypt(void *src, void *dst, int len, u32 flags);//one char by char

int crypto_aes_expand_key_generic(struct crypto_aes_ctx *ctx, const u8 *in_key,
		unsigned int key_len);
int crypto_aes_set_key_generic(const u8 *in_key,
		unsigned int key_len);
void aes_encrypt_generic(u8 *out, const u8 *in);
void aes_decrypt_generic(u8 *out, const u8 *in);

//struct timespec start, end;
struct timespec switch_start, switch_end;
static DECLARE_WAIT_QUEUE_HEAD(wq);
//static DEFINE_MUTEX(Isem);
static DEFINE_MUTEX(Qsem);
/*spearte extract part and dequeue_complete part will not allow huge data block
*/
static int interrupt_manag(struct crypto_priv *localCpg)
{	
	int numOfRun_I=0;
	int dataSize=0;
	int id=localCpg->ID;
	int numOfTask_I;
	//printk(KERN_INFO "First time in interrupt manager %d",id);
	do{	
		//printk(KERN_INFO "I%d start checking");	
		__set_current_state(TASK_INTERRUPTIBLE);
		if(localCpg->numOfTask==0)
			goto Ifinish;
Iacquire:
		/*GO*/
		//printk(KERN_INFO "============I%d is try to get the lock",id);
		//mutex_lock(&Isem);//if I cannot get the lock, it will schedule here and been sending into the wait queue of Isem
		//printk(KERN_INFO "++++++++++I%d is getting the lock, start processing",id);		

		//printk(KERN_INFO "I%d start data prepare,numOftask is %d ",id,localCpg->numOfTask);
		//getnstimeofday(&start);
		//mutex_lock(&localCpg->mutexOfReg);
		DataPrepare(localCpg,localCpg->request_collector);
		//mutex_unlock(&localCpg->mutexOfReg);
		//getnstimeofday(&end);
		//long difference = end.tv_nsec - start.tv_nsec;
		//printk(" in DataPrepare is %ld,numOftask is %d\n", difference,localCpg->numOfTask);
		
		//printk(KERN_INFO "I%d: totalRequestSize is %d",id,localCpg->totalRequestSize);
		//getnstimeofday(&start);
		do_crypt(localCpg->sourceBuf, localCpg->destBuf, localCpg->totalRequestSize, localCpg->firstFlag);
		//getnstimeofday(&end);
		//difference = end.tv_nsec - start.tv_nsec;
		//printk("in do_crypt	%ld \n", difference);
		//printk(KERN_INFO "totalRequestSize for cpg%d is cleared",id);
		localCpg->totalRequestSize=0;
		//printk(KERN_INFO "I%d: PROCESSDONE \n",id);	
		localCpg->eng_st = ENGINE_W_DEQUEUE;//now it's turn for Q to do dequeue
		//printk(KERN_INFO "I%d try to wake up Q",id);
//		while(//localCpg->stopOfQ){
		//wake_up_process(localCpg->queue_th);
		//wake_up_all(&wq);
//		}
//		//printk(KERN_INFO "I%d success wake up Q",id);	
		//mutex_unlock(&Isem);
		//printk(KERN_INFO "--------I%d release the lock, stop processing",id);
//		if(cpg[!id]->IFlag&&!cpg[!id]->terminate){
//		//printk(KERN_INFO "I%d try to wake up I*",id);
//			while(cpg[0]->stopOfI)
		wake_up_all(&wq);
		//wake_up_process(cpg[!id]->interrupt_th);
//		//printk(KERN_INFO "I%d try to wake up I*",id);	
//			}
Ifinish:		
		//printk(KERN_INFO "I%d is going to wait for IFlag",id);
		//localCpg->stopOfI=1;
		wait_event_interruptible(wq,localCpg->IFlag||com->exitFlag);
		spin_lock_irq(&com->lockOfIFlag);
		localCpg->IFlag=0;
		spin_unlock_irq(&com->lockOfIFlag);	
		//localCpg->stopOfI=0;
		if(com->exitFlag)
		 goto iexit;
		//wait_event_tony(localCpg,0,localCpg->IFlag||com->exitFlag);
		//printk(KERN_INFO "I%d is waking up from waiting for IFlag",id);
		goto Iacquire;	
		
//	if(com->exitFlag)
	//printk(KERN_INFO "rmmod being called,I%d exit.",id);
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
	int maxData=BUF_SIZE;//assuming each request have 512 bytes data
	int id=localCpg->ID;//0 or 1
//	int numOfRun_Q=0;
	localCpg->eng_st = ENGINE_IDLE;
	cPointer=localCpg->request_collector;
	//printk(KERN_INFO "First time in queue manager %d",id);	
	localCpg->Qstart=1;
	do {	
		__set_current_state(TASK_INTERRUPTIBLE);
qdequeue:
		/*dequeue_complete*/
		if(localCpg->eng_st == ENGINE_W_DEQUEUE){
/*			if(localCpg->currentOrder!=(com->totalNumOfMapping+localCpg->counter)){//error may mix up data order
					//printk(KERN_INFO "!!!!Error, order may mix, go to release!!");
					goto qrelease;
				}*/
//			long difference;
			//printk("Q%d start dequeue_complete_req,counter is %d\n",id,localCpg->counter);
//			getnstimeofday(&start);
		//	mutex_lock(&localCpg->mutexOfReg);
			dequeue_complete_req(localCpg,localCpg->request_collector);
		//	mutex_unlock(&localCpg->mutexOfReg);
//			getnstimeofday(&end);
			//printk ("Q%d finish dequeue_complete_req ,counter is %d\n",id,localCpg->counter);
			
//			difference = end.tv_nsec - start.tv_nsec;
			//printk ("%ld for dequeue_complete_req is \n", difference);	
			localCpg->eng_st=ENGINE_IDLE;
			//printk(KERN_INFO "Q%d exit DequeueALL",id);
		}
qacquire:		 	
		//printk(KERN_INFO "===========Q%d is trying to get lock,idle? %d",id,localCpg->eng_st==ENGINE_IDLE);
		mutex_lock(&Qsem);
		//printk(KERN_INFO "+++++++++++Q%d get lock,idle? %d",id,localCpg->eng_st==ENGINE_IDLE);
		/*collect*/
		if (localCpg->eng_st == ENGINE_IDLE) {		
qcollect:
			spin_lock_irq(&com->lockOfH);
			backlog = crypto_get_backlog(&com->queue);
			async_req = crypto_dequeue_request(&com->queue);
			spin_unlock_irq(&com->lockOfH);			
			if (async_req) {			
				req= ablkcipher_request_cast(async_req);	
			//	//printk(KERN_INFO "request coming size is %d",req->nbytes);
				req_ctx= ablkcipher_request_ctx(req);	
			//	BUG_ON(localCpg->eng_st != ENGINE_IDLE);
				*cPointer=async_req;/*address in async_req copied into request_collector */	
				cPointer++;
			//	//printk(KERN_INFO"cPointer is point to somewhere of request_collector address is %p",cPointer);
				localCpg->totalRequestSize += req->nbytes;
//				//printk(KERN_INFO "total data size is %d",localCpg->totalRequestSize);				
				localCpg->numOfTask++;
//				spin_lock_irq(&com->lockOfOrder);
//				com->totalNumOfRequest++;
//				spin_unlock_irq(&com->lockOfOrder);
				if(localCpg->numOfTask==1) {
					localCpg->firstFlag=req_ctx->decrypt;
				}
//				//printk(KERN_DEBUG "Q%d is collecting one,numOfTask is %d,totalNumOfRequest is %d",id,localCpg->numOfTask,com->totalNumOfRequest);				
				if(localCpg->totalRequestSize >= maxData || req_ctx->decrypt != localCpg->firstFlag){//operation change
					forceProcess=1;
//					BUG_ON(localCpg->totalRequestSize > maxData);
				}
			}
			else //async_req is null
			{//no more request
				//printk(KERN_INFO "Q%d getting no more request, queue size is %d localCpg->numOfTask is %d",id,queue->qlen,localCpg->numOfTask);
				if(localCpg->numOfTask>0){//if currently does have tasks.
					forceProcess=1;
				}
				//else just do nothing.
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
			spin_lock_irq(&com->lockOfIFlag);			
			localCpg->IFlag=1;
			spin_unlock_irq(&com->lockOfIFlag);
			//printk(KERN_INFO "Q%d is going to wake up I",id);
//			while(//localCpg->stopOfI){
			//wake_up_process(localCpg->interrupt_th);//may be replaced by wake_up_all
//			}
//			//printk(KERN_INFO "Q%d is successfully wake up I",id);
			//wake_up_all(&wq);
			cPointer = localCpg->request_collector;	
//			spin_lock_irq(&com->lockOfOrder);
//			localCpg->currentOrder=com->totalNumOfRequest;
//			spin_unlock_irq(&com->lockOfOrder);
//			//printk(KERN_INFO "Q%d is currently point to %ld",id,localCpg->currentOrder);
			goto qrelease;
		}else{	
//				//printk(KERN_INFO "Q%d is still idle goto terminate checking",id);
				goto tcheck;
			}
qrelease:
			/*release*/
			mutex_unlock(&Qsem);
			wake_up_all(&wq);
//			//printk(KERN_INFO "---------------------Q%d release lock,idle? %d",id,localCpg->eng_st==ENGINE_IDLE);
			//if(cpg[!id]->Qstart&&!cpg[!id]->terminate){
//				//printk(KERN_INFO "Q1 is going to wake up Q0");
//					while(cpg[0]->stopOfQ){
						//wake_up_process(cpg[!id]->queue_th);
//					}
//					if(cpg[0]->terminate)
//					//printk(KERN_INFO "Q0 terminate, Q1 is not going to wake it up");
//				//printk(KERN_INFO "Q1 success wake up Q0");	
				//}	
//			//printk(KERN_INFO "Q%d is going to sleep wait for enginestat become W_DEQUEUE",id);
			//localCpg->stopOfQ=1;
			wait_event_interruptible(wq,localCpg->eng_st == ENGINE_W_DEQUEUE||com->exitFlag);
			//localCpg->stopOfQ=0;
			if(com->exitFlag)
				goto qexit;
			//wait_event_tony(localCpg,1,localCpg->eng_st == ENGINE_W_DEQUEUE||com->exitFlag);
			//BUG_ON(!(localCpg->eng_st==ENGINE_W_DEQUEUE||com->exitFlag));
//			//printk(KERN_INFO "Q%d is waking up as engst is w_dequeue",id);
			goto qdequeue;
tcheck:
		if(!queue->qlen&&!localCpg->numOfTask)
		{	
//			//printk(KERN_INFO "Q%d is going to terminate",id);
			/*release*/
			mutex_unlock(&Qsem);
//			//printk(KERN_INFO "-----------------Q%d release lock,idle? %d",id,localCpg->eng_st==ENGINE_IDLE);
			//if(cpg[!id]->Qstart)//just to prevent error
				//wake_up_process(cpg[!id]->queue_th);
			wake_up_all(&wq);
errback:	
//			//printk(KERN_INFO "Q%d nothing to handle sleep",id);	
			//spin_lock_irq(&com->lockOfQ);
			//localCpg->terminate=1;		
			
			//spin_unlock_irq(&com->lockOfQ);
		/*	if(cpg[0]->terminate&&cpg[1]->terminate){
				spin_lock_irq(&com->lockOfOrder);
				com->totalNumOfRequest=0;
				com->totalNumOfMapping=0;
				spin_unlock_irq(&com->lockOfOrder);
				}*/
			//localCpg->stopOfQ=1;
			if(!id)//Q0 is prepare for every single request
			wait_event_interruptible(wq,queue->qlen!=0||com->exitFlag);
			else//all the rest is only wake up when huge data coming
			wait_event_interruptible(wq,queue->qlen>8||com->exitFlag);
			//localCpg->stopOfQ=0;
			//spin_lock_irq(&com->lockOfQ);	
			//localCpg->terminate=0;
			//spin_unlock_irq(&com->lockOfQ);
			if(com->exitFlag)
				goto qexit;
			//wait_event_tony(localCpg,1,queue->qlen!=0||com->exitFlag);//no more request to process
//			//printk(KERN_INFO "Q%d is waking up from doing nothing, queue size is %d",id,queue->qlen);
			cPointer = localCpg->request_collector;
			goto qacquire;
			//printk(KERN_INFO"cPointer of Q%d is point to starting of request_collector address is %p",id,cPointer);		
		}else{
			goto qcollect;
		}
		/*else if(localCpg->eng_st==ENGINE_IDLE){
				//this may not necessary
//				//printk(KERN_INFO "Q%d is still idle haven't release the lock goto collect again but not require lock",id);
		}else if(localCpg->eng_st==ENGINE_W_DEQUEUE){
//				//printk(KERN_INFO "Q%d is W-dequeue state haven't release the lock goto w_dequeue but not require lock",id);
				goto qdequeue;
		}else{	
			//printk(KERN_INFO "!!!!!");
			BUG_ON(1);
		}*/
		/**/
	} while (!kthread_should_stop());
qexit:
	if(com->exitFlag)
	printk(KERN_INFO "rmmod being called Q%d exit \n.",id);	
	//printk(KERN_INFO "Exiting Queue Manager%d \n.",id);
	return 0;
}

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
//	//printk(KERN_INFO "!!!!!!enqueue being called, queue size is %d \n",queue->qlen);
	//printk(KERN_INFO "S0 is %d,S1 is %d,Is0 is %d, Is1 is %d",cpg[0]->stopOfQ,cpg[1]->stopOfQ,cpg[0]->stopOfI,cpg[1]->stopOfI);
//	if(cpg[0]->stopOfQ&&cpg[1]->stopOfQ&&cpg[0]->stopOfI&&cpg[1]->stopOfI)
//	{
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

	crypto_aes_expand_key(&gen_aes_key, ctx->aes_enc_key, ctx->key_len);

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
}
static int mv_dec_aes_ecb(struct ablkcipher_request *req)
{
	int flags;
	struct mv_ctx *ctx = crypto_tfm_ctx(req->base.tfm);
	struct mv_req_ctx *req_ctx = ablkcipher_request_ctx(req);
	struct crypto_queue *queue=&com->queue;
	//printk(KERN_INFO "dec aes ecb method being called");
	req_ctx->op = COP_AES_ECB;
	req_ctx->decrypt = 1;
	compute_aes_dec_key(ctx);
	//printk(KERN_INFO "dec aes ecb method being alled:The size of queue is %d",queue->qlen);
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
		localCpg->p.complete(localCpg->ID);
		local_bh_disable();
		asreq->complete(asreq, 0);
		local_bh_enable();				
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
	ctx->key_len = len;
	ctx->need_calc_aes_dkey = 1;
	//printk(KERN_WARNING "dsi_setkey_blk: setting key, len = %d.", len);
	crypto_aes_set_key_generic(key, len);
//	//printk(KERN_INFO "crypto set key being called");
	memcpy(ctx->aes_enc_key, key, AES_KEY_LEN);
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
static struct pci_driver dsi_aes_driver = {
	.name = "DSI AES Driver",
	.id_table = dsi_aes_tbl,
	.probe = dsi_aes_probe,
	.remove = __devexit_p(dsi_aes_remove)
};

MODULE_ALIAS("platform:mv_crypto");

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
		spin_lock_init(&com->lockOfIFlag);
//		spin_lock_init(&com->lockOfReadI);
		//spin_lock_init(&com->lockOfacquireI);
		//spin_lock_init(&com->lockOfacquireQ);
		crypto_init_queue(&com->queue,50);
		//printk(KERN_WARNING "queue initialized\n");	
		int i;
		for(i=0;i<numOfCpg;i++){
		localCpg = kzalloc(sizeof(struct crypto_priv), GFP_KERNEL);
		if (!localCpg)
			return -ENOMEM;
		localCpg->ID=i;
		localCpg->queue_th = kthread_run(queue_manag, localCpg, "mv_crypto");
		localCpg->interrupt_th = kthread_run(interrupt_manag, localCpg, "mv_crypto");
		mutex_init(&localCpg->mutexOfReg);	
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
		kthread_stop(localCpg->queue_th);
		kthread_stop(localCpg->interrupt_th);
		}
}

module_exit(dsi_crypto_exit);

MODULE_AUTHOR("");
MODULE_DESCRIPTION("");
MODULE_LICENSE("GPL");
