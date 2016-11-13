%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

iris-local-init: clean
	git submodule update --init iris
	ln -nsf iris iris-enabled

iris-local-update:
	git submodule update --remote --merge

iris-local:
	+make -C iris -f Makefile

iris-system-init: clean
	rm -f iris-enabled

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony iris-local iris-local-init iris-local-update iris-system
