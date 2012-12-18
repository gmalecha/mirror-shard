GENERIC := Reflection GenRec Tactics ListFacts Folds Multimap \
	   Decidables DepList EqdepClass NatMap
PROVERS := Assumption Reflexivity ArrayBound Locals
MEMEVALS := PtsTo Array Locals
#  Transitivity
MODULES    := Ordering \
	Nomega Word Labels LabelMap \
	PropX PropXRel PropXTac XCAP \
	Memory DiscreteMemory \
	Structured StructuredModule Linker \
	Programming Arrays \
	Reflect \
	Heaps SepTheory SepTheoryXIL \
	Env TypedPackage \
	Expr ReifyExpr ExprUnify \
	Prover \
	$(MEMEVALS:%=sep/%) \
	$(PROVERS:%=provers/%Prover) \
	SepExpr ReifySepExpr SepHeap SepUnify SepCancel \
	Unfolder UnfolderTac ReifyHints SepLemma \
	SymEval SymIL SymILProofs SymILTac \
	IL ReifyIL ILEnv SepIL \
	CancelTac CancelIL \
	ILTacCommon ILTac \
	TypedPackage TacPackIL Allocated \
	AMD64_gas

TESTS := UnfolderTests
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R . Bedrock

.PHONY: coq clean package native ltac version

coq: Makefile.coq ILTac.v
	$(MAKE) -f Makefile.coq

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
