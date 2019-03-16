include Makefile.ml-files

OCAMLBUILD = ocamlbuild -tag safe_string -package batteries -I coq -I ml

default: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq all

stores: launchStore1.native launchStore2.native launchStore3.native

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

$(ALGSML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

benchgen.native : ml/*.ml
	$(OCAMLBUILD) benchgen.native

launchStore1.native: $(ALG1) ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" $(ALG1ML)
	$(OCAMLBUILD) launchStore1.native

launchStore2.native: $(ALG2) ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" $(ALG2ML)
	$(OCAMLBUILD) launchStore2.native

launchStore3.native: $(ALG3) ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" $(ALG3ML)
	$(OCAMLBUILD) launchStore3.native

experiment.native: ml/*.ml
	$(OCAMLBUILD) experiment.native 

run: launchStore1.native launchStore2.native launchStore2.native benchgen.native
	./batchrun

run2: launchStore1.native launchStore2.native launchStore2.native benchgen.native
	./batchrundetach

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	$(OCAMLBUILD) launchStore1.native -clean
	$(OCAMLBUILD) launchStore2.native -clean
	$(OCAMLBUILD) launchStore3.native -clean
	$(OCAMLBUILD) benchgen.native -clean
	$(OCAMLBUILD) experiment.native -clean
	rm -f Makefile.coq Makefile.coq.conf
	rm -f RemoteAllOutputs.txt
	rm -f RemoteAllResults.txt
	rm -f RemoteLauncherOutput.txt

.PHONY: default coq run run2 clean install stores $(ALGSML)
.NOTPARALLEL: $(ALGSML)
