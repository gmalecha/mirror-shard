GENERIC := Tactics ListFacts Folds Multimap \
	   MoreFMapFacts NatMap
PROVERS := Assumption Reflexivity
#  Transitivity
MODULES    := Ordering \
	DiscreteMemory MultiMem \
	Reify Quantifier \
	Heaps SepTheory \
	Env TypedPackage \
	Expr ReifyExpr \
	Instantiation SimpleInstantiation SimpleBlockInstantiation \
	ExprUnify \
	ExprUnifySyn ExprUnifySynGenRec \
	Prover ProvePures \
	$(PROVERS:%=provers/%Prover) \
	Provers \
	SepExpr ReifySepExpr SepHeap SepUnify \
	SepCancel OrderedCanceler \
	Unfolder UnfolderTac ReifyHints Lemma SepLemma \
	CancelTacBedrock \
	TypedPackage \
	ExprTac SepExprTac

#CancelLoopTac \

TESTS := UnfolderTests
VS         := $(GENERIC:%=%.v) $(MODULES:%=%.v)
TVS        := $(TESTS:%=%.v)

ARGS :=-R ../coq-ext-lib/theories ExtLib \
       -R . MirrorShard

.PHONY: coq clean package

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq
	$(MAKE) -f Makefile.coq install

Makefile.coq: Makefile $(VS)
	coq_makefile $(ARGS) $(VS) \
        | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
        > Makefile.coq

Makefile.test.coq: Makefile $(TVS)
	coq_makefile $(ARGS) $(TVS) -o Makefile.test.coq \
        | sed -re 's/-R ([^ ]+) ExtLib/-I \1 -as ExtLib/g' \
        > Makefile.test.coq

test: coq Makefile.test.coq
	$(MAKE) -f Makefile.test.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend

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
