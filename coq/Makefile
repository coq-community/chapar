MODULES    := Lib/extralib Lib/Varith Lib/Vbase Lib/Vlistbase Lib/Vlist \
	Lib/Predefs \
	ReflectiveAbstractSemantics \
	KVStore KVSAlg1 KVSAlg2 KVSAlg3 \
	Extract \
	Examples/Clients \
	Examples/ListClient
VS         := $(MODULES:%=%.v)

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	coq_makefile -I Lib $(VS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
