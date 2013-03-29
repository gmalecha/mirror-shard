GENERIC := Reflection GenRec Tactics ListFacts Folds Multimap \
	   Decidables DepList EqdepClass NatMap
PROVERS := Assumption Reflexivity
#  Transitivity
MODULES    := Ordering \
	DiscreteMemory MultiMem \
	Reify Quantifier \
	Heaps SepTheory \
	Env TypedPackage \
	Expr ReifyExpr ExprUnify \
	Prover \
	$(PROVERS:%=provers/%Prover) \
	Provers \
	SepExpr ReifySepExpr SepHeap SepUnify SepCancel \
	Unfolder UnfolderTac ReifyHints SepLemma \
	CancelTacBedrock \
	TypedPackage \
	ExprTac SepExprTac

#CancelLoopTac \

TESTS := UnfolderTests
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . MirrorShard

.PHONY: coq clean package native ltac version

coq: Makefile.coq ILTac.v
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) -o Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend ILTac.v ILTac.vo ILTac.v.d ILTac.glob

native:
	@ echo "## "
	@ echo "## Switching to OCaml reification."
	@ echo "## "
	@ rm -f ILTac.v ILTac.vo ILTac.v.d ILTac.glob
	@ ln -s ILTacML.v ILTac.v
	@ make -C reification

ltac:
	@ echo "## "
	@ echo "## Switching to ltac reification."
	@ echo "## "
	@ rm -f ILTac.v ILTac.vo ILTac.v.d ILTac.glob
	@ ln -s ILTacLtac.v ILTac.v

ILTac.v:
	@ echo "## "
	@ echo "## Warning: No ILTac.v, defaulting to Ltac reification."
	@ echo "## NOTE: If you would like to use the faster, ML reification"
	@ echo "##       run 'make native'"
	@ echo "## "
	@ $(MAKE) native

version:
	@ echo "## "
	@ echo "## You are running" $(patsubst ILTac%.v,%,$(shell readlink ILTac.v)) "reification"
	@ echo "## "

package:
	hg archive -t tgz /tmp/bedrock.tgz

admit:
	@ grep -n -e 'admit' -e 'Admitted' ${VS}

depgraph: Makefile.coq
	@ echo Generating dependency graph to ../deps.pdf
	@ ./../tools/deps.py $(MODULES:%=%.v.d) > ../deps.dot
	@ ./../tools/deps.py $(MODULES:%=%.v.d) | dot -Tpdf -o ../deps.pdf

toplevel: coq
	coqtop.opt $(ARGS)
