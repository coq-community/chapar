# OCAMLBUILD = ocamlbuild -lib unix -I coq -I ml/MLLib/ocamlbase -I ml/MLLib/batteries -I ml
OCAMLBUILD = ocamlbuild -lib unix -I coq -I ml/MLLib/batteries -I ml


default: launchStore.native benchgen.native experiment.native


coq:
	make -C coq

benchgen.native : coq ml/*.ml
	$(OCAMLBUILD) benchgen.native

launchStore.native : coq ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" coq/KVSAlg1.ml
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" coq/KVSAlg2.ml
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" coq/KVSAlg3.ml
	$(OCAMLBUILD) launchStore1.native
	$(OCAMLBUILD) launchStore2.native
	$(OCAMLBUILD) launchStore3.native

experiment.native: ml/*.ml
	$(OCAMLBUILD) experiment.native 

run: launchStore.native benchgen.native
	./batchrun

run2: launchStore.native benchgen.native
	./batchrundetach



clean:
	make -C coq clean
	$(OCAMLBUILD) launchStore1.native -clean
	$(OCAMLBUILD) launchStore2.native -clean
	$(OCAMLBUILD) launchStore3.native -clean
	$(OCAMLBUILD) benchgen.native -clean
	$(OCAMLBUILD) experiment.native -clean
	rm -f *.native
	rm -f RemoteAllOutputs.txt
	rm -f RemoteAllResults.txt
	rm -f RemoteLauncherOutput.txt

.PHONY : default coq run run2 clean



