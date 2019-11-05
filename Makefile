all: default

default: Makefile.coq
	$(MAKE) -f Makefile.coq
	dune build src/main.exe

run: Makefile.coq
	$(MAKE) -f Makefile.coq
	./run.sh

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install


clean_coq: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall


clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	./clean.sh
	rm -f Makefile.coq Makefile.coq.conf _CoqProject
	dune clean

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: prebuild.sh
	./prebuild.sh

.PHONY: all default quick install clean run clean_coq
