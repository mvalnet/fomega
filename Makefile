SHELL := bash

DUNE  := opam exec dune -- build --display short

# [make all] compiles your project.

.PHONY: all
all:
	@ $(DUNE) src/main.exe

# [make lazy src=test/inputs/foo.fw] typechecks the file [foo.fw] with option --lazy
# [make lazy inputs=foo.fw] typechecks the file [foo.fw] with option --lazy

.PHONY: lazy eager
lazy eager:
	@ dune exec src/main.exe -- --$@ ${src} \
	    $(patsubst %, test/inputs/%, ${program})

# [make clean] cleans up.

.PHONY: clean
clean:
	@ find . -name "*~" -exec rm '{}' \;
	@ dune clean

# [make test] runs all tests.

# If an expected-output file is missing, then an empty file is created.

.PHONY: test
test:
	@ for f in test/inputs/*.fw ; do \
	    for mode in lazy eager; do \
	      touch "$${f%.fw}.$${mode}.exp" ; \
	    done \
	  done
	@ $(DUNE) @runtest

lazytest:
	@ for f in test/inputs/*.fw ; do \
	    touch "$${f%.fw}.lazy.exp" ; \
	  done
	@ $(DUNE) @runtest

eagertest:: 
	@ for f in test/inputs/*.fw ; do \
	    touch "$${f%.fw}.eager.exp" ; \
	  done
	@ $(DUNE) @runtest

speed:

# [make promote] updates the expected-output files used by [make test].

.PHONY: promote
promote:
	@ dune promote

# [make depend] regenerates the files dune.auto. This command should
# be run every time some test files are added or removed or renamed.

.PHONY: depend
depend:
	@ $(DUNE) @depend --auto-promote || true
