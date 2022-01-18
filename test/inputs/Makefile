ROOT = ../..
FOMEGA = $(ROOT)/_build/default/src/main.exe

FILES = $(wildcard *.fw)
LAZY = $(patsubst %.fw, %.fwi, $(FILES))
EAGER = $(patsubst %.fw, %.fwe, $(FILES))
LAST = $(shell ls -t $(FILES) | head -1)

.PHONY: last all lazy eager parse

last: $(filter $(patsubst %.fw, %, $(LAST)).%, $(LAZY))
	@ echo '# Showing' $<
	@ cat $<

all: lazy

lazy: $(LAZY)

eager: $(EAGER)


$(FOMEGA):
	make -C $(ROOT) 

# Just typecheck
%.fwi: %.fw $(FOMEGA)
	@ echo '# Typecking' $<
	@ $(FOMEGA) $<  >$@  || \
	(cat $@ && rm $@ && false)

%.fwe: %.fw $(FOMEGA)
	@ echo '# Typecking' $<
	@ $(FOMEGA) --eager $<  >$@  || \
	(cat $@ && rm $@ && false)

# To typecheck and display
%.fwio: %.fwi
	@ cat $< 

%.fweo: %.fwe
	@ cat $< 

# Show timing
timing: reduce_expensive.fwe
	tail -3 $<

# Compute timing
%.fwe: %.FW
	@ echo '# Timing... make take a few minites' $<
	bash -c "time $(FOMEGA) --lazy $<" >$*.fwi 2>&1 
	@ tail -3 $*.fwi
	bash -c "time $(FOMEGA) --eager $<" >$*.fwe 2>&1  
	@ tail -3 $*.fwe


clean::
	rm -f *.fw[ies] *.s.fw
