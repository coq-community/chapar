include Makefile.ml-files

MLFILES = ml/algorithm.ml ml/algorithm1.ml ml/algorithm2.ml ml/algorithm3.ml \
 ml/common.ml ml/benchgen.ml ml/benchprog.ml ml/commonbench.ml ml/configuration.ml \
 ml/launchStore1.ml ml/launchStore2.ml ml/launchStore3.ml ml/runtime.ml \
 ml/experiment.ml ml/readConfig.ml ml/util.ml

OCAMLBUILD = ocamlbuild -tag safe_string -package batteries -I ml

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

benchgen.native : $(MLFILES)
	$(OCAMLBUILD) benchgen.native

launchStore1.native: $(ALG1) $(MLFILES) benchgen.native
	$(OCAMLBUILD) launchStore1.native

launchStore2.native: $(ALG2) $(MLFILES) benchgen.native
	$(OCAMLBUILD) launchStore2.native

launchStore3.native: $(ALG3) $(MLFILES) benchgen.native
	$(OCAMLBUILD) launchStore3.native

experiment.native: $(MLFILES)
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
