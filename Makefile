MODULE:=MirrorShard

.PHONY: all clean dist

all:
	# BEWARE: This will probably take a long time (and may require up to 4GB of memory)!
	$(MAKE) -C src
	$(MAKE) -C examples

clean:
	$(MAKE) -C src clean
	$(MAKE) -C examples clean

dist:
	git archive --prefix mirror-shard/ HEAD -o mirror-shard.tgz

.dir-locals.el: tools/dir-locals.el Makefile
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el | sed s,MOD,$(MODULE),g > .dir-locals.el

install:
	$(MAKE) -C src install

init:
	@ ./tools/setup.sh
	@ (cd coq-ext-lib; $(MAKE))
