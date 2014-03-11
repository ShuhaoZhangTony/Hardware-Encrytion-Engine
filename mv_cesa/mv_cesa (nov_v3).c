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
#define numOfCpg 1
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
#define DSI_AES_ALG_ENABLE
#define DSI_AES_ECB_ENABLE
// #define DSI_AES_CBC_ENABLE

#define DSI_HW_CRYPT_VENDOR_ID		0x10EE
#define DSI_HW_CRYPT_DEVICE_ID		0x6018
#define DSI_HW_CRYPT_SUBVENDOR_ID 	0x10EE
#define DSI_HW_CRYPT_SUBDEVICE_ID 	0x0007

#define HAVE_REGION 0x01                    // I/O Memory region
#define HAVE_IRQ    0x02                    // Interupt
#define HAVE_KREG   0x04                    // Kernel registration

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
#define AESKEY0_0		0x60 /* AES key MSW */
#define ICSR            0x40
#define ICLR            0x48

#define DREGCOUNT 18
#define DMA_REGISTER_SIZE         (4 * DREGCOUNT)    // There are eighteen registers, and each is 4 bytes wide.

#define MaxTag 64
#define BUF_SIZE		1024*1023
#define TAG_SIZE 		4096
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
struct request_handler//contain list_head
{
	struct crypto_async_request *request_collector;	
	struct req_progress p;
	struct list_head mylist; 
	u32 index;
};
struct request_handler staticRH[MaxTag];
struct crypto_priv {
	/**critical members*/
	struct task_struct *queue_th;
	struct task_struct *dequeue_th;
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
//	spinlock_t lockOfIFlag;//IFlag
};

static struct crypto_priv *cpg[10];
//	long totalNumOfMapping;
static	struct list_head *WTI; 
static	struct list_head *RTI;
static	struct list_head *CTI;
struct common_struct {
	struct task_struct *interrupt_th;
	int PrePIndex;
	u32 status;
	u32 preStatus;
	u32 HWsimulate_status;
	/* the lock protects queue and eng_st */
	spinlock_t lockOfW;//lock of WTI
	spinlock_t lockOfH;//queue
	spinlock_t lockOfD;//lock of RTI
	spinlock_t lockOfS;//lockOfsimulateStatus
	spinlock_t lockOfP;//lock of PrePIndex
	spinlock_t lockOfN;//lock of numoftask
	struct crypto_queue queue;//com own the queue
	int exitFlag;
//	long totalNumOfRequest;
	/*counters*/
	int numOfTask;
	int tooClose;
};
static struct common_struct *com;
static struct request_handler *ListHead;
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

static inline void dequeue_complete_req(u32 index);
static inline void DataPrepare(u32 index);
static int do_crypt(void *src, void *dst, int len, u32 flags,u32 index);//one char by char

int crypto_aes_expand_key_generic(struct crypto_aes_ctx *ctx, const u8 *in_key,
		unsigned int key_len);
int crypto_aes_set_key_generic(const u8 *in_key,
		unsigned int key_len);
void aes_encrypt_generic(u8 *out, const u8 *in);
void aes_decrypt_generic(u8 *out, const u8 *in);

struct timespec start, end;
//struct timespec switch_start, switch_end;
static DECLARE_WAIT_QUEUE_HEAD(wq);//first use only one wait queue and check the performance.
/**
*Throughout this program, all write operation is not under lock,but all read operation is.
*I think lock or not is depends on different situation.
*/
static int dequeue_manag(struct crypto_priv *localCpg)
{
	int DFlag=0;
	int tooClose=0;
	struct request_handler *rh = NULL;
	int id=localCpg->ID;
	//WTI point to 63, CTI point to 63 RTI point to 62
	//WTI point to 61, CTI point to 63 RTI point to 62
	//if RTI 62->63 then WTI may 61->62 while 62 may still under processing
	//so 62->62 but tooClose being set untile dequeue finish RTI 62->63
	//CTI 63->10, RTI ->63,WTI ->62
	//RTI 
	do{
		printk(KERN_INFO "D%d is tryting to get the lock",id);
		spin_lock_irq(&com->lockOfD);
		printk(KERN_INFO "D%d get the lock",id);
		if(RTI!=CTI&&!com->tooClose){
		//too close is to prevent when D-man is still processing on last-one,
		//P-man shouldn't go on to prepare it
			rh = list_entry (RTI, struct request_handler , mylist );
			if(RTI->prev==WTI){
				printk(KERN_INFO "RTI is too close to WTI");
				tooClose=1;
				com->tooClose=1;
			}
			else{
				RTI=RTI->next;
				struct request_handler *rh=list_entry(RTI,struct request_handler,mylist);
				printk(KERN_INFO "RTI is point to %d\n",rh->index);
			}
			DFlag=1;
		}		
		spin_unlock_irq(&com->lockOfD);
		printk(KERN_INFO "D%d release the lock",id);
		if(DFlag){
			DFlag=0;
			printk(KERN_INFO "dequeue_com being called by Dman, with index of %d,numOfTask is %d",rh->index,com->numOfTask);
			dequeue_complete_req(rh->index);
			if(tooClose){
				tooClose=0;
				RTI=RTI->next;
#if 0			//for testing only	
				struct request_handler *rh=list_entry(RTI,struct request_handler,mylist);
				printk(KERN_INFO "RTI is point to %d\n",rh->index);
#endif	
				com->tooClose=0;
			}
		}
		wait_event(wq,RTI!=CTI||com->exitFlag);
		printk(KERN_INFO "D%d is waking up as RTI!=CTI",id);
		__set_current_state(TASK_UNINTERRUPTIBLE);
	} while (!kthread_should_stop());
}
static int interrupt_manag(void *data)
{	
	printk(KERN_INFO "First time in interrupt manager");
	com->status =0x3f;
	com->preStatus = 0x3f;
	int i;
	int cont;
	do{
		if (key_size == AES_KEYSIZE_256){ //enable this if-else if HW is ready
			printk(KERN_INFO "Iman is checking");
			/*read statuts*/
			__set_current_state(TASK_INTERRUPTIBLE);
			do{
				com->status = dma_rd_reg(DCSR);
				//spin_lock_irq(&com->lockOfS);
				//com->status=com->HWsimulate_status;
				//spin_unlock_irq(&com->lockOfS);
				printk(KERN_INFO "Interrupt manager:com->status is %d\n",com->status);
				msleep(100);//use schedule_timeout_uninterruptible
			}while(com->status==com->preStatus&&!com->exitFlag);
			BUG_ON(com->status<0||com->status>63);
			printk(KERN_INFO "Iman finish checking, status is %d \n",com->status);
			cont=0;
			//printk(KERN_INFO "HW process:wrbuf after do_crypt:");
			//DMEM32(&wr_buf[(com->status)*TAG_SIZE],4096);
#if 0			
			if(wr_buf[(com->status)*TAG_SIZE]==0){
			printk(KERN_INFO ":tag shift happen");	
			memcpy(&wr_buf[(com->status)*TAG_SIZE],&wr_buf[(com->status-1)*TAG_SIZE],TAG_SIZE);

			printk(KERN_INFO "HW process:wrbuf after modify: com->status is %d ",com->status);
			DMEM32(&wr_buf[(com->status)*TAG_SIZE],4096);
			}
#endif
			if(com->status<com->preStatus){//over run
				for(i=com->preStatus+1;i<MaxTag;i++){
					CTI=CTI->next;
					cont++;
					}
				wake_up_all(&wq);//wake up D man
				for(i=0;i<=com->status;i++){
					CTI=CTI->next;
					cont++;
					}
#if 0	//for testing only
				struct request_handler *rh=list_entry(CTI->prev,struct request_handler,mylist);
				BUG_ON(!rh->index==com->status);
				printk(KERN_INFO "OK, CTI is point to next free slot CPI is point to %d\n",rh->index+1);
#endif	
			wake_up_all(&wq);//wake up D man
			}else{//normal condition
				for(i=com->preStatus+1;i<=com->status;i++){
					CTI=CTI->next;
					cont++;
				}
#if 0	//for testing only			
				struct request_handler *rh=list_entry(CTI->prev,struct request_handler,mylist);
				BUG_ON(!rh->index==com->status);
				printk(KERN_INFO "OK, CTI is point to next free slot CPI is point to %d\n",rh->index+1);
#endif	
				wake_up_all(&wq);//wake up D man
			}
				spin_lock_irq(&com->lockOfN);
				com->numOfTask-=cont;
				spin_unlock_irq(&com->lockOfN);
				cont=0;
				printk(KERN_INFO "com->numOfTask is now:%d",com->numOfTask);
				com->preStatus=com->status;	
		}

		//printk(KERN_INFO "I man is waitting for numOfTask");
		wait_event(wq,com->numOfTask||com->exitFlag);
		printk(KERN_INFO "I manager is waking up with numOfTask of %d",com->numOfTask);	
		if(com->exitFlag)
			goto Iexit;	
	} while (!kthread_should_stop());
Iexit:
	printk(KERN_INFO "Exiting interrupt Manager.");
	return 0;
}

static int queue_manag(struct crypto_priv *localCpg)
{
	struct crypto_async_request *async_req = NULL;
	struct crypto_async_request *backlog = NULL;
	static	struct list_head *testPointer = NULL; 
	struct request_handler *rh = NULL;
	struct ablkcipher_request *req = NULL;	
	struct mv_req_ctx *req_ctx = NULL;
	struct crypto_queue *queue=&com->queue;
	int id=localCpg->ID;
	int i;
	int QFlag=0;
	int ret;
	if(id==0){
		com->PrePIndex=0x3f;
		com->HWsimulate_status=0x3f;//given same simulate value for software testing purpose.
		//ONLY Q0 will prepare the linked list
		/*Prepare head*/
		ListHead=&staticRH[0];
		ListHead->mylist.next=&ListHead->mylist;
		ListHead->mylist.prev=&ListHead->mylist;
		ListHead->index=0;
		printk(KERN_INFO "head is prepared, index is %d\n",staticRH[0].index);
		/*Add the rest to head, build a circular linked list*/
		testPointer=&ListHead->mylist;
		for(i=1;i<MaxTag;i++){
			list_add_tail(&staticRH[i].mylist, &ListHead->mylist);
			testPointer=testPointer->next;
			rh=list_entry(testPointer,struct request_handler,mylist);
			rh->index=i;
		}
		WTI=RTI=CTI=&ListHead->mylist;//everyone of them point to first one;
#if 0
		//enable if you want to test the initiation.
		//testing
		for(i=0;i<200;i++){
		rh=list_entry(WTI,struct request_handler,mylist);
		printk(KERN_INFO "i is %d, index is %d, index from staticRH is %d\n",i,rh->index,staticRH[i%MaxTag].index);
		WTI=WTI->next;
		}
		WTI=RTI=CTI=&ListHead->mylist;//everyone of them point to first one;
#endif
#ifdef DSI_DMA_ENABLE
		//enable if HW is ready
		com->status = dma_rd_reg(DCSR);
		printk(KERN_INFO "Before Qman start read status is %d\n",com->status);
	//	BUG_ON(com->status!=0x3f);
		for(i=0;i<MaxTag;i++){
		WTI=WTI->next;
		}
		RTI=CTI=WTI;
		rh=list_entry(WTI,struct request_handler,mylist);
		printk(KERN_INFO "index is %d, start with 0\n",rh->index);
#endif	
}
	do {
		printk(KERN_INFO "Q%d is tryting to get the lockofW",id);
		spin_lock_irq(&com->lockOfW);
		printk(KERN_INFO "Q%d get the lockofW",id);
		if(WTI->next!=RTI->prev){
			spin_lock_irq(&com->lockOfH);
			backlog = crypto_get_backlog(&com->queue);
			async_req = crypto_dequeue_request(&com->queue);
			spin_unlock_irq(&com->lockOfH);			
			if (async_req) {
				QFlag=1;
				printk(KERN_INFO "Q%d is going to prepare one request",id);
				req= ablkcipher_request_cast(async_req);	
				req_ctx= ablkcipher_request_ctx(req);
				rh = list_entry ( WTI, struct request_handler , mylist );
				printk(KERN_INFO "rh = %p; index = %d", rh, rh ? rh->index : 100);
				rh->request_collector=async_req;/*address in async_req copied into request_collector */			
			//enable this if-end if HW is ready to test
			if(key_size == AES_KEYSIZE_256)// only when using hardware en/de WTI is moving
					WTI=WTI->next;
			}
			spin_unlock_irq(&com->lockOfW);
			printk(KERN_INFO "Q%d release the lockofW",id);
		}else{
			spin_unlock_irq(&com->lockOfW);
			printk(KERN_INFO "Q%d release the lockofW",id);
			printk(KERN_INFO "WTI need to wait,dequeue_comple too slow");
				wait_event(wq,WTI->next!=RTI->prev||com->exitFlag);
		}
		if(QFlag){
			QFlag=0;
			printk(KERN_INFO "before list_entry; nbytes = %d", req->nbytes);
			/*DataPrepare for this request*/
			//memset(&rd_buf[rh->index*TAG_SIZE],0,TAG_SIZE);
			printk(KERN_INFO "before dataPrepare:");
			//DMEM32(&rd_buf[rh->index*TAG_SIZE],req->nbytes);
			DataPrepare(rh->index);
			printk(KERN_INFO "after dataPrepare:");
			//DMEM32(&rd_buf[rh->index*TAG_SIZE],req->nbytes);
			/*send request to hardware*/
			//memset(&wr_buf[(rh->index-1)*TAG_SIZE],0,TAG_SIZE*2);
			//memset(&wr_buf[0*TAG_SIZE],0,TAG_SIZE);
			printk(KERN_INFO "wrbuf 0 after do_crypt:");
			//DMEM32(&wr_buf[0*TAG_SIZE],4096);
			printk(KERN_INFO "wrbuf before do_crypt:");
			//DMEM32(&wr_buf[rh->index*TAG_SIZE],req->nbytes);
			if (key_size == AES_KEYSIZE_256){
			printk(KERN_INFO "Q%d before wait_event prePIndex is %d,rh->index is %d ",id,com->PrePIndex,rh->index);
				int ret;
				while(!ret)
				ret=wait_event_timeout(wq,rh->index==((com->PrePIndex+1)%MaxTag)||com->exitFlag,1000);
			spin_lock_irq(&com->lockOfP);//this lock is not necessary .	
			com->PrePIndex=rh->index;
			spin_unlock_irq(&com->lockOfP);
			printk(KERN_INFO "Q%d after wait_event prePIndex is %d",id,com->PrePIndex);
			wake_up_all(&wq);
			}
			do_crypt(&rd_buf[rh->index*TAG_SIZE],&wr_buf[rh->index*TAG_SIZE],req->nbytes,req_ctx->decrypt,rh->index);
			if(key_size == AES_KEYSIZE_256){// enable when HW is ready	
#if 0
					spin_lock_irq(&com->lockOfS);
					com->HWsimulate_status=rh->index;
					spin_unlock_irq(&com->lockOfS);
					printk(KERN_INFO "HW simulate status is now :%d\n",com->HWsimulate_status);
#endif	
					spin_lock_irq(&com->lockOfN);
					com->numOfTask++;
					BUG_ON(com->numOfTask>64);
					spin_unlock_irq(&com->lockOfN);
					printk(KERN_INFO "wake up I manager");
					wake_up_all(&wq);//wake up I manager
				}// enable when HW is ready
			else{
				printk(KERN_INFO "software do_crypt finish, start dequeue_com, software shouldn't change rh->index :%d",rh->index);	
				dequeue_complete_req(rh->index);
				//printk(KERN_INFO "S/W wrbuf after do_crypt:");
				//DMEM32(&wr_buf[rh->index*TAG_SIZE],req->nbytes);
			}
		}
		if (backlog) {
			backlog->complete(backlog, -EINPROGRESS);
			backlog = NULL;
		}
		printk(KERN_INFO "Q%d manager is going to wait",id);
		wait_event(wq,queue->qlen||com->exitFlag);
		printk(KERN_INFO "Q%d manager is waking up with queue lenth is %d\n",id,queue->qlen);
		__set_current_state(TASK_UNINTERRUPTIBLE);
	} while (!kthread_should_stop());
	printk(KERN_INFO "Exiting Q Manager \n.");
	return 0;
}

static int
do_crypt(void *src, void *dst, int len, u32 flags,u32 index)
{
	u32 counter = 50000;
	int iLenCtr, old_len;
	long nSec;
	unsigned long iflags;
	struct timespec tsBefore, tsAfter;
	struct crypto_queue *queue=&com->queue;

#if 1
	//spin_lock_irqsave(&lock, iflags);	
	if (key_size == AES_KEYSIZE_256) {
	printk(KERN_WARNING "do crypt: start hardware encrypt/decrypt; flags = %08x; len = %d, queue size is %d with index of %d", flags, len,queue->qlen,index);
	//dma_wr_reg(RDMATLPS, len|0x00000000); 
	//u32 test;
	//test=len|0x00000000|index<<16;
	//printk(KERN_INFO "test signal is %X",test);
	if(!flags){
		dma_wr_reg(RDMATLPS, len | 0x00000000| index << 16); // caveat: make sure flags contain direction & start bits
	}else{
		dma_wr_reg(RDMATLPS, len | 0x80000000| index << 16); // caveat: make sure flags contain direction & start bits
		}
		printk(KERN_INFO "do_crypt finish");	
		return 0;
	}
	else{ //uncoment if H/W is ready
#endif
		printk(KERN_INFO "start software encrypt/decrypt,with index of %d",index);
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
			return 0;		
	}
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
	wake_up_all(&wq);
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
	printk(KERN_INFO "%s: setting key, len = %d.\n",__func__, ctx->key_len);
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
static void mv_crypto_algo_completion(u32 index)
{
	sg_miter_stop(&staticRH[index].p.src_sg_it);
	sg_miter_stop(&staticRH[index].p.dst_sg_it);
}
static inline void DataPrepare(u32 index)	
{	
	struct req_progress *p =&staticRH[index].p;
	struct ablkcipher_request *req;
	int num_sgs;
	int ret;
	void *sbuf;
	int copy_len;
	int len;
	char *dbuf;
	memset(p, 0, sizeof(struct req_progress));//initial p to 0
	p->complete = mv_crypto_algo_completion;//static void mv_crypto_algo_completion(int)
		req =ablkcipher_request_cast(staticRH[index].request_collector);
		len = req->nbytes;//
		num_sgs = count_sgs(req->src, req->nbytes);
		sg_miter_start(&p->src_sg_it, req->src, num_sgs, SG_MITER_FROM_SG);
		printk(KERN_INFO "index is %d ",index);
		dbuf=&rd_buf[index*TAG_SIZE];
		printk(KERN_INFO "read buffer is %p",&rd_buf[index*TAG_SIZE]);
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
}
static inline void dequeue_complete_req(u32 index)	
{
	struct req_progress *p = &staticRH[index].p;
	struct ablkcipher_request *req; 
	int num_sgs;
	int ret;
	int dst_copy;
	int len;	
	void *dbuf;	
	char *sbuf;
		req =ablkcipher_request_cast(staticRH[index].request_collector);
		len=req->nbytes;	
		num_sgs = count_sgs(req->dst, req->nbytes);
		sg_miter_start(&p->dst_sg_it, req->dst, num_sgs, SG_MITER_TO_SG);		
		sbuf=&wr_buf[TAG_SIZE*index];
		while(len)
		{
			if (!p->sg_dst_left) 
			{
				ret = sg_miter_next(&p->dst_sg_it);
				BUG_ON(!ret);
				p->sg_dst_left = p->dst_sg_it.length;
				p->dst_start = 0;
			}
				dbuf = p->dst_sg_it.addr+ p->dst_start;
				dst_copy = min(len, p->sg_dst_left);
				memcpy(dbuf,sbuf,dst_copy);
				p->dst_start += dst_copy;
				p->sg_dst_left -= dst_copy;
				len -= dst_copy;
				sbuf +=dst_copy;
		}
		local_bh_disable();
		staticRH[index].request_collector->complete(staticRH[index].request_collector,0);
		local_bh_enable();				
		p->complete(index);	
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
	printk(KERN_WARNING "dsi_setkey_blk: setting key as %x, len = %d.", *key,key_size);

//	printk(KERN_INFO "%s: setting key before set key generic, len = %d.", __func__, len);
	//DMEM32(key, len);
	crypto_aes_set_key_generic(key, len);
	printk(KERN_INFO "%s: setting key after set key generic, len = %d.", __func__, len);
	//DMEM32(key, len);

	printk(KERN_INFO "crypto set key being called");
	memcpy(ctx->aes_enc_key, key, len);
	
	if (len == AES_KEYSIZE_256) {
		//mutex_lock(&Isem);
	 	printk(KERN_INFO "dsi_setkey_blk: inside len = aes_keysize_256 condition");
		printk(KERN_INFO "key is %ld",*key);
		_writefield(AESKEY0_0, key); // we can only support 256 bits now
		//mutex_unlock(&Isem);
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
static void __devexit
dsi_aes_remove(struct pci_dev *dev)
{
	crypto_unregister_alg(&mv_aes_alg_ecb);
	com->exitFlag=1;
	wake_up_all(&wq);
//	wake_up_all(&wq);
//	wake_up_all(&wq);
//	wake_up_all(&wq);
	int i;
	for(i=0;i<numOfCpg;i++){
		kthread_stop(cpg[i]->queue_th);
		kthread_stop(cpg[i]->dequeue_th);
	}
	kthread_stop(com->interrupt_th);
	if (stat_flags & HAVE_REGION)
		release_mem_region(dsi_aes_dma.addr, DMA_REGISTER_SIZE);
	pci_free_consistent(dev, BUF_SIZE, rd_buf, rd_hw_addr);
	pci_free_consistent(dev, BUF_SIZE, wr_buf, wr_hw_addr);
	
	//staticRH=NULL;
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
	//dma_wr_reg(virt_to_phys(wr_hw_addr), WDMATLPDA);	
	printk(KERN_INFO "set the start address of FPGA write done\n");
	com = kzalloc(sizeof(struct common_struct), GFP_KERNEL);
	if (!com)
		return -ENOMEM;
	com->exitFlag=0;
	com->interrupt_th = kthread_run(interrupt_manag, com, "mv_crypto");
	spin_lock_init(&com->lockOfH);
	spin_lock_init(&com->lockOfW);
//	spin_lock_init(&com->lockOfReadI);
	//spin_lock_init(&com->lockOfacquireI);
	//spin_lock_init(&com->lockOfacquireQ);
	crypto_init_queue(&com->queue,50);
	printk(KERN_WARNING "queue initialized\n");	
		
	int i;
	for(i=0;i<numOfCpg;i++){	
		cpg[i] = kzalloc(sizeof(struct crypto_priv), GFP_KERNEL);
		if (!cpg[i])
			return -ENOMEM;
		//spin_lock_init(&cpg[i]->lockOfIFlag);
		cpg[i]->ID=i;
		cpg[i]->queue_th = kthread_run(queue_manag, cpg[i], "mv_crypto");
		cpg[i]->dequeue_th = kthread_run(dequeue_manag, cpg[i], "mv_crypto");
	}

	printk(KERN_WARNING "dsi-aes: register algorithm.\n");

	ret = crypto_register_alg(&mv_aes_alg_ecb);
	if (ret)
		goto ewrmemrel;

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
