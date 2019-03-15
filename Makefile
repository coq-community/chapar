OCAMLBUILD = ocamlbuild -tag safe_string -package batteries -I coq -I ml

default: coq

stores: launchStore1.native launchStore2.native launchStore3.native

coq:
	$(MAKE) -C coq

install:
	$(MAKE) -C coq install

benchgen.native : coq ml/*.ml
	$(OCAMLBUILD) benchgen.native

launchStore1.native: coq ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" coq/KVSAlg1.ml
	$(OCAMLBUILD) launchStore1.native

launchStore2.native: coq ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" coq/KVSAlg2.ml
	$(OCAMLBUILD) launchStore2.native

launchStore3.native: coq ml/*.ml benchgen.native
	sed -i "s/failwith \"AXIOM TO BE REALIZED\"/4/g" coq/KVSAlg3.ml
	$(OCAMLBUILD) launchStore3.native

experiment.native: ml/*.ml
	$(OCAMLBUILD) experiment.native 

run: launchStore1.native launchStore2.native launchStore2.native benchgen.native
	./batchrun

run2: launchStore1.native launchStore2.native launchStore2.native benchgen.native
	./batchrundetach

clean:
	$(MAKE) -C coq clean
	$(OCAMLBUILD) launchStore1.native -clean
	$(OCAMLBUILD) launchStore2.native -clean
	$(OCAMLBUILD) launchStore3.native -clean
	$(OCAMLBUILD) benchgen.native -clean
	$(OCAMLBUILD) experiment.native -clean
	rm -f RemoteAllOutputs.txt
	rm -f RemoteAllResults.txt
	rm -f RemoteLauncherOutput.txt

.PHONY: default coq run run2 clean install stores
