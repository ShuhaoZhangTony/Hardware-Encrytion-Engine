obj-m += mv_crypto.o
mv_crypto-objs := mv_cesa.o aes_generic.o

all:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) modules

clean:
	make -C /lib/modules/$(shell uname -r)/build M=$(PWD) clean
