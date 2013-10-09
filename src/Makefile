PACKAGES   := FP/Classes FP/Data
FILES      := $(foreach pkg,$(PACKAGES),$(patsubst %.v,%,$(wildcard $(pkg)/*.v))) \
	            $(patsubst %.v,%,$(wildcard *.v))
SOURCES    := $(FILES:%=%.v) 

COQ_ARGS :=
COQ_MAKEFILE_ARGS := -R FP FP -arg "$(COQ_ARGS)"

.PHONY: all clean html check-admit

all: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

check-admit:
	grep -n -e 'admit' -e 'Admitted' ${SOURCES}

Makefile.coq: Makefile $(SOURCES)
	coq_makefile $(COQ_MAKEFILE_ARGS) $(SOURCES) -o Makefile.coq


