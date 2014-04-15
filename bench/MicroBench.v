Require Import Coq.Lists.List.
Require Import evm_compute.Evm_compute.
Require Import MirrorShard.Expr.
(* Require Import MirrorShard.CancelTacIL. *)

Add ML Path "reification".
Declare ML Module "extlib".
Declare ML Module "reif".

Parameter ptsto : nat -> nat -> hprop.
Parameter mptsto : bool -> nat -> nat -> hprop.

Definition types : list Expr.type.
refine (
  (@Typ nat EqNat.beq_nat _ ::
  (@Typ bool (fun x y => match x , y with | true, true | false , false => true | _ , _ => false end) _ ::
  (@Typ (list nat) (fun x y => false) _ ::
  (@Typ (list bool) (fun x y => false) _ ::
   nil))))); admit.
Defined.

Definition iif : bool -> nat -> nat -> nat:=
  (fun x y z => if x then y else z).

Definition funcs : list (Expr.signature types).
refine (
   @Sig types (tvType 0 :: tvType 0 :: nil) (tvType 0) plus ::
  (@Sig types (tvType 0 :: tvType 0 :: nil) (tvType 0) minus ::
  (@Sig types (tvType 0 :: tvType 0 :: nil) (tvType 0) mult ::
  (@Sig types (tvType 0 :: tvType 0 :: nil) (tvType 1) EqNat.beq_nat ::
  (@Sig types (tvType 1 :: tvType 0 :: tvType 0 :: nil) (tvType 0) iif ::
   nil))))).
Defined.

Definition preds : list (SEP.predicate types).
refine (
   @SEP.PSig types (tvType 0 :: tvType 0 :: nil) ptsto ::
  (@SEP.PSig types (tvType 1 :: tvType 0 :: tvType 0 :: nil) mptsto :: nil)).
Defined.

Fixpoint chainl {ts} (ls : list (Expr.expr ts)) {struct ls} : SEP.sexpr ts :=
  match ls with
    | nil => SEP.Emp
    | a :: b =>
      match b with
        | nil => SEP.Emp
        | c :: d => SEP.Star (SEP.Func 0 (a :: c :: nil)) (chainl b)
      end
  end%Sep.

Definition chainr {ts} (ls : list (Expr.expr ts)) {struct ls} : SEP.sexpr ts :=
  rev (chainl ls).

Fixpoint list_to (now : nat) (n : nat) : list (Expr.expr types) :=
  match n with
    | 0 => nil
    | S n => @Expr.Const types (tvType 0) (S n) :: list_to now n
  end.

Definition nsexprD (emp : hprop) (star : hprop -> hprop -> hprop) (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) :=
  fun (types : list Expr.type) (funcs : Expr.functions types)
    (sfuncs : SEP.predicates types) =>
    fix sexprD (meta_env var_env : Expr.env types) (s : SEP.sexpr types)
    {struct s} : hprop :=
    match s with
      | SEP.Emp => emp
      | SEP.Inj p =>
        match Expr.exprD funcs meta_env var_env p Expr.tvProp with
          | Some p0 => inj p0
          | None => inj (SepExpr.BadInj p)
        end
      | SEP.Star l r =>
        star (sexprD meta_env var_env l) (sexprD meta_env var_env r)
      | SEP.Exists t b =>
        ex _
        (fun x : Expr.tvarD types t =>
          sexprD meta_env (@existT _ (Expr.tvarD types) t x :: var_env) b)
      | SEP.Func f b =>
        match nth_error sfuncs f with
          | Some f' =>
            match
              Expr.applyD (Expr.exprD funcs meta_env var_env)
              (SEP.SDomain f') b hprop (SEP.SDenotation f')
              with
              | Some p => p
              | None => inj (SepExpr.BadPredApply f b var_env)
            end
          | None => inj (SepExpr.BadPred f)
        end
      | SEP.Const p => p
    end.

Definition cancel (himp : hprop -> hprop -> Prop) (emp : hprop) (star : hprop -> hprop -> hprop)
  (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop)
  (ts : list Expr.type)
  (funcs : Expr.functions ts)
  (preds : SEP.predicates ts)
  (uvars : Expr.env ts)
  (hyps : Expr.exprs ts)
  (lhs rhs : SEP.sexpr ts): Prop :=
  let types := ts in
  let bound := 10 in
  let hints :=
    {| TacPackIL.UNF.Forward := nil
     ; TacPackIL.UNF.Backward := nil |} in
  let prover := Provers.trivialProver ts in
  let tfuncs := typeof_funcs funcs in
  let tpreds := SEP.typeof_preds preds in
  if SEP.WellTyped_sexpr tfuncs tpreds (typeof_env uvars) nil rhs then
  match CANCEL_TAC.canceller tpreds (TacPackIL.UNF.Forward hints) (TacPackIL.UNF.Backward hints) prover (typeof_env uvars) hyps lhs rhs with
                  | None =>
                    himp (nsexprD emp star ex inj _ funcs preds uvars nil lhs)
                    (nsexprD emp star ex inj _ funcs preds uvars nil rhs)
                  | Some {| CANCEL_TAC.AllExt := new_vars
                    ; CANCEL_TAC.ExExt := new_uvars
                    ; CANCEL_TAC.Lhs := lhs'
                    ; CANCEL_TAC.Rhs := rhs'
                    ; CANCEL_TAC.Subst := subst |} =>
                  forallEach new_vars (fun nvs : env ts =>
                    let var_env := nvs in
                      AllProvable_impl funcs uvars var_env
                      (CANCEL_TAC.existsSubst funcs var_env subst 0
                        (map
                          (fun x : sigT (tvarD types) =>
                            existT (fun t : tvar => option (tvarD types t))
                            (projT1 x) (Some (projT2 x))) uvars ++
                          map
                          (fun x : tvar =>
                            existT (fun t : tvar => option (tvarD types t)) x None)
                          new_uvars)
                        (fun meta_env0 : env types =>
                          AllProvable_and funcs meta_env0 var_env
                          (himp
                            (nsexprD emp star ex inj _ funcs preds meta_env0 var_env
                              (SH.sheapD
                                {|
                                  SH.impures := SH.impures lhs';
                                  SH.pures := nil;
                                  SH.other := SH.other lhs' |}))
                            (nsexprD emp star ex inj _ funcs preds meta_env0 var_env
                              (SH.sheapD
                                {|
                                  SH.impures := SH.impures rhs';
                                  SH.pures := nil;
                                  SH.other := SH.other rhs' |})))
                          (SH.pures rhs'))) (SH.pures lhs'))

                end
                else
                  himp (nsexprD emp star ex inj _ funcs preds uvars nil lhs)
                  (nsexprD emp star ex inj _ funcs preds uvars nil rhs).

Ltac evaluate_evm :=
  evm blacklist [himp;emp;star;ex;inj;ptsto;mptsto;plus;minus;mult;EqNat.beq_nat;iif].
Ltac evaluate_vm := vm_compute.
Ltac evaluate_cbv :=
  cbv beta iota zeta
       delta [
         Quantifier.quantD Quantifier.appendQ
         Quantifier.qex Quantifier.qall
         Quantifier.gatherAll Quantifier.gatherEx

         (** ILEnv **)
         ILEnv.comparator ILEnv.fPlus ILEnv.fMinus ILEnv.fMult
         ILEnv.bedrock_types_r ILEnv.bedrock_funcs_r
         ILEnv.bedrock_types
         ILEnv.BedrockCoreEnv.core
         ILEnv.BedrockCoreEnv.pc ILEnv.BedrockCoreEnv.st
         ILEnv.bedrock_type_W ILEnv.bedrock_type_nat
         ILEnv.bedrock_type_setting_X_state
         ILEnv.bedrock_type_state
(*         ILEnv.bedrock_type_test *)
         ILEnv.bedrock_type_reg

(*         ILEnv.test_seq *)
         ILEnv.reg_seq
         ILEnv.W_seq

         ILEnv.word_nat_r
         ILEnv.word_state_r
(*         ILEnv.word_test_r *)

         ILEnv.wplus_r
         ILEnv.wminus_r
         ILEnv.wmult_r
(*         ILEnv.word_test_r *)
(*         ILEnv.wcomparator_r *)
         ILEnv.Regs_r
         ILEnv.wlt_r
         ILEnv.natToW_r

         (** Env **)
         Env.repr_combine Env.default Env.footprint Env.repr'
         Env.updateAt Env.nil_Repr Env.repr Env.updateAt
         Env.repr_combine Env.footprint Env.default Env.repr

         (** Expr **)
         Expr.Range Expr.Domain Expr.Denotation Expr.Impl
         Expr.exists_subst Expr.forallEach Expr.existsEach
         Expr.AllProvable_and Expr.AllProvable_impl Expr.AllProvable_gen
         Expr.tvarD Expr.exprD Expr.applyD Expr.Impl_ Expr.EqDec_tvar
         Expr.tvar_rec Expr.tvar_rect Expr.liftExpr Expr.lookupAs Expr.Eqb
         Expr.Provable Expr.tvar_val_seqb
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs Expr.AllProvable Expr.AllProvable_gen
         Expr.Provable Expr.tvarD
         Expr.expr_seq_dec
         Expr.applyD Expr.exprD Expr.Range Expr.Domain Expr.Denotation
         Expr.lookupAs
         Expr.tvarD Expr.Eqb
         Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.Default_signature Expr.EmptySet_type Expr.Impl Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
         Expr.expr_seq_dec  Expr.expr_seq_dec
         Expr.tvar_val_seqb  Expr.liftExpr Expr.exprSubstU
         Expr.typeof Expr.typeof_env
         Expr.typeof_sig Expr.typeof_funcs
         Expr.Impl_ Expr.exprD
         Expr.expr_ind
         Expr.expr_seq_dec
         Expr.get_Eq
         Expr.const_seqb
         Expr.tvar_seqb
         Expr.tvar_val_seqb_correct
         Expr.tvar_seqb_correct
         Expr.mentionsU
         ReifyExpr.default_type


         (** ExprUnify **)
(*
         CancelTacIL.CANCEL_LOOP.U.exprUnify CancelIL.U.exprUnify_recursor
         CancelIL.U.exprInstantiate CancelIL.U.subst_exprInstantiate
         CancelIL.U.Subst_lookup CancelIL.U.subst_lookup
         CancelIL.U.Subst_empty CancelIL.U.subst_empty
         CancelIL.U.Subst_set CancelIL.U.subst_set
         CancelIL.U.Subst_equations
         CancelIL.U.Subst_size
         CancelIL.U.dep_in

         CancelIL.U.FM.Raw.height CancelIL.U.FM.Raw.cardinal CancelIL.U.FM.Raw.assert_false CancelIL.U.FM.Raw.create
         CancelIL.U.FM.Raw.bal CancelIL.U.FM.Raw.remove_min CancelIL.U.FM.Raw.merge CancelIL.U.FM.Raw.join
         CancelIL.U.FM.Raw.t_left CancelIL.U.FM.Raw.t_opt CancelIL.U.FM.Raw.t_right
         CancelIL.U.FM.Raw.cardinal CancelIL.U.FM.Raw.empty CancelIL.U.FM.Raw.is_empty
         CancelIL.U.FM.Raw.mem CancelIL.U.FM.Raw.find
         CancelIL.U.FM.Raw.add  CancelIL.U.FM.Raw.remove
         CancelIL.U.FM.Raw.fold CancelIL.U.FM.Raw.map CancelIL.U.FM.Raw.mapi CancelIL.U.FM.Raw.map2

         CancelIL.U.FM.this CancelIL.U.FM.is_bst
         CancelIL.U.FM.empty CancelIL.U.FM.is_empty
         CancelIL.U.FM.add CancelIL.U.FM.remove
         CancelIL.U.FM.mem CancelIL.U.FM.find
         CancelIL.U.FM.map CancelIL.U.FM.mapi CancelIL.U.FM.map2
         CancelIL.U.FM.elements CancelIL.U.FM.cardinal CancelIL.U.FM.fold
         CancelIL.U.FM.equal
         CancelIL.U.FM.E.eq_dec
*)

         (** Unfolder **)
         Unfolder.FM.empty Unfolder.FM.add Unfolder.FM.remove
         Unfolder.FM.fold Unfolder.FM.map
         Unfolder.FM.find
(*         UNF.LEM.Foralls  *) UNF.Vars
         UNF.UVars UNF.Heap (* UNF.LEM.Hyps UNF.LEM.Lhs UNF.LEM.Rhs *)
         UNF.Forward UNF.forward UNF.unfoldForward UNF.Backward
         UNF.backward UNF.unfoldBackward  equiv_dec
         UNF.find UNF.findWithRest UNF.findWithRest'
         Folds.allb
         UNF.openForUnification
         UNF.quant
         UNF.liftInstantiate
         SH.applySHeap
         UNF.find UNF.default_hintsPayload
         UNF.applicable UNF.checkAllInstantiated

         (** NatMap **)
         NatMap.singleton
         NatMap.IntMap.Raw.height NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.assert_false NatMap.IntMap.Raw.create
         NatMap.IntMap.Raw.bal NatMap.IntMap.Raw.remove_min NatMap.IntMap.Raw.merge NatMap.IntMap.Raw.join
         NatMap.IntMap.Raw.t_left NatMap.IntMap.Raw.t_opt NatMap.IntMap.Raw.t_right
         NatMap.IntMap.Raw.cardinal NatMap.IntMap.Raw.empty NatMap.IntMap.Raw.is_empty
         NatMap.IntMap.Raw.mem NatMap.IntMap.Raw.find
         NatMap.IntMap.Raw.add  NatMap.IntMap.Raw.remove
         NatMap.IntMap.Raw.fold NatMap.IntMap.Raw.map NatMap.IntMap.Raw.mapi NatMap.IntMap.Raw.map2

         NatMap.IntMap.this NatMap.IntMap.is_bst
         NatMap.IntMap.empty NatMap.IntMap.is_empty
         NatMap.IntMap.add NatMap.IntMap.remove
         NatMap.IntMap.mem NatMap.IntMap.find
         NatMap.IntMap.map NatMap.IntMap.mapi NatMap.IntMap.map2
         NatMap.IntMap.elements NatMap.IntMap.cardinal NatMap.IntMap.fold
         NatMap.IntMap.equal

         Int.Z_as_Int._0 Int.Z_as_Int._1 Int.Z_as_Int._2 Int.Z_as_Int._3
         Int.Z_as_Int.plus Int.Z_as_Int.max
         Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec

         ZArith_dec.Z_gt_le_dec ZArith_dec.Z_ge_lt_dec ZArith_dec.Z_ge_dec
         ZArith_dec.Z_gt_dec
         ZArith_dec.Zcompare_rec ZArith_dec.Zcompare_rect

         BinInt.Z.add BinInt.Z.max BinInt.Z.pos_sub
         BinInt.Z.double BinInt.Z.succ_double BinInt.Z.pred_double

         BinInt.Z.compare

         BinPos.Pos.add BinPos.Pos.compare
         BinPos.Pos.succ BinPos.Pos.compare_cont

         Compare_dec.nat_compare CompOpp

         NatMap.Ordered_nat.compare

         sumor_rec sumor_rect
         sumbool_rec sumbool_rect
         eq_ind_r

         (** Prover **)
         Prover.Prove Prover.Prover Prover.Facts Prover.Learn Prover.Summarize
         Prover.composite_ProverT

         (** Provers **)
         Provers.ComboProver

(*
         (** TransitivityProver **)
         provers.TransitivityProver.transitivitySummarize
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.transitivityProve
         provers.TransitivityProver.groupsOf
         provers.TransitivityProver.addEquality
         provers.TransitivityProver.proveEqual
         provers.TransitivityProver.transitivityLearn
         provers.TransitivityProver.inSameGroup
         provers.TransitivityProver.in_seq
         provers.TransitivityProver.groupWith
         provers.TransitivityProver.transitivityProver
*)

         (** AssumptionProver **)
         provers.AssumptionProver.assumptionProver
         provers.AssumptionProver.assumptionSummarize
         provers.AssumptionProver.assumptionLearn
         provers.AssumptionProver.assumptionProve

         (** ReflexivityProver **)
         provers.ReflexivityProver.reflexivityProver
         provers.ReflexivityProver.reflexivitySummarize
         provers.ReflexivityProver.reflexivityLearn
         provers.ReflexivityProver.reflexivityProve

         (** WordProver **)
         provers.WordProver.wordProver provers.WordProver.Source provers.WordProver.Destination provers.WordProver.Difference
         provers.WordProver.pow32 provers.WordProver.wplus' provers.WordProver.wneg' provers.WordProver.wminus' wordBin NToWord Nplus minus
         provers.WordProver.decompose combine Expr.expr_seq_dec provers.WordProver.combineAll provers.WordProver.combine app
         provers.WordProver.alreadyCovered provers.WordProver.alreadyCovered' andb orb provers.WordProver.merge provers.WordProver.wordLearn1 provers.WordProver.wordLearn
         provers.WordProver.equalitysEq ILEnv.W_seq Word.weqb weq provers.WordProver.equalityMatches provers.WordProver.wordProve provers.WordProver.wordSummarize
         provers.WordProver.types ILEnv.bedrock_type_W provers.WordProver.zero Bool.bool_dec wzero' posToWord bool_rec bool_rect
         Nminus wordToN Nsucc Nmult Pos.mul Pos.add Pos.sub_mask Pos.succ_double_mask Pos.double_mask Pos.pred_double
         provers.WordProver.natToWord' mod2 Div2.div2 whd wtl Pos.double_pred_mask
         provers.WordProver.Equalities provers.WordProver.LessThans provers.WordProver.NotEquals
         provers.WordProver.lessThanMatches

         (** ArrayBoundProver **)
         provers.ArrayBoundProver.boundProver
         provers.ArrayBoundProver.deupd provers.ArrayBoundProver.factIn
         provers.ArrayBoundProver.boundLearn1 provers.ArrayBoundProver.boundLearn
         provers.ArrayBoundProver.boundSummarize provers.ArrayBoundProver.hypMatches
         provers.ArrayBoundProver.boundProve
         provers.ArrayBoundProver.types

         (** Induction **)
         list_ind list_rec list_rect
         sumbool_rect sumbool_rec
         sumor_rec sumor_rect
         nat_rec nat_rect nat_ind
         eq_rect_r eq_rec_r eq_rec eq_rect
         eq_sym f_equal
         nat_rect eq_ind eq_rec eq_rect
         eq_rec_r eq_rect eq_rec nat_rec nat_rect
         sumbool_rec sumbool_rect
         sumbool_rec sumbool_rect
         sumor_rec sumor_rect
         nat_rec nat_rect

         (** Comparisons **)
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_dec Compare_dec.le_dec Compare_dec.le_gt_dec
         Compare_dec.le_lt_dec Compare_dec.lt_eq_lt_dec
         Compare_dec.lt_eq_lt_dec
         Peano_dec.eq_nat_dec
         EquivDec_nat  equiv_dec seq_dec
         nat_eq_eqdec
         EquivDec_SemiDec
         Compare_dec.nat_compare
         NPeano.leb NPeano.ltb

         (** SepExpr **)
         SEP.SDomain SEP.SDenotation
         SEP.Default_predicate
         SEP.himp SEP.sexprD
         SEP.heq
         nat_eq_eqdec
         SEP.liftSExpr

         (** SepHeap **)
         SH.impures SH.pures SH.other
         SH.liftSHeap UNF.HEAP_FACTS.sheapSubstU
         SH.hash
         SH.star_SHeap
         SH.SHeap_empty
         SH.sheapD

         SepHeap.FM.empty
         SepHeap.FM.map
         SepHeap.FM.find
         SepHeap.FM.add
         SepHeap.FM.remove
         SepHeap.FM.fold

         (** SepCancel **)
(*         CancelIL.CANCEL.sepCancel
         CancelIL.CANCEL.expr_count_meta
         CancelIL.CANCEL.exprs_count_meta
         CancelIL.CANCEL.expr_size
         CancelIL.CANCEL.meta_order_funcs
         CancelIL.CANCEL.meta_order_args
         CancelIL.CANCEL.order_impures
         CancelIL.CANCEL.cancel_in_order
         CancelIL.CANCEL.unify_remove
         CancelIL.CANCEL.unifyArgs
         CancelIL.CANCEL.expr_size

         CancelIL.canceller
         CancelIL.substInEnv
         CancelIL.existsMaybe
         CancelIL.existsSubst
         *)
         (** Ordering **)
         Ordering.insert_in_order Ordering.list_lex_cmp Ordering.sort

         (** Multimaps **)
         SepHeap.MM.mmap_add SepHeap.MM.mmap_extend SepHeap.MM.mmap_join
         SepHeap.MM.mmap_mapi SepHeap.MM.mmap_map
         SepHeap.MM.empty

         (** PtsTo Plugin **)
         Plugin_PtsTo.ptsto32_ssig
         Plugin_PtsTo.expr_equal Plugin_PtsTo.sym_read_word_ptsto32
         Plugin_PtsTo.sym_write_word_ptsto32 Plugin_PtsTo.ptsto32_types_r
         Plugin_PtsTo.types
         Plugin_PtsTo.MemEval_ptsto32
         Plugin_PtsTo.MemEvaluator_ptsto32

         (** General Recursion **)
         Fix Fix_F GenRec.wf_R_pair GenRec.wf_R_nat
         GenRec.guard Acc_rect well_founded_ind
         well_founded_induction_type Acc_inv ExprUnify.wf_R_expr

         (** Folds **)
         Folds.fold_left_2_opt Folds.fold_left_3_opt

         (** List Functions **)
         tl hd_error value error hd
         nth_error Datatypes.length fold_right firstn skipn rev
         rev_append List.map app fold_left

         (** Aux Functions **)
         fst snd projT1 projT2 Basics.impl value error
         projT1 projT2 andb orb
         plus minus

         (** Reflection **)
         (* Reflection.Reflect_eqb_nat *)

         (** Array *)
         Array.ssig Array.types_r Array.types
         Array.MemEval Array.MemEvaluator
         Array.div4 Array.deref Array.sym_read Array.sym_write
         Array.wlength_r Array.sel_r Array.upd_r

         (** Locals *)
         Locals.bedrock_type_string Locals.bedrock_type_listString Locals.bedrock_type_vals
         Locals.ssig Locals.types_r Locals.types
         Locals.MemEval Locals.MemEvaluator
         Locals.ascii_eq Locals.string_eq Bool.eqb
         Locals.nil_r Locals.cons_r Locals.sel_r Locals.upd_r
         Locals.deref Locals.listIn Locals.sym_sel Locals.sym_read Locals.sym_write

         (** ?? **)
         DepList.hlist_hd DepList.hlist_tl
         eq_sym eq_trans
         EqNat.beq_nat

         (** TODO: sort these **)
         ILAlgoTypes.Env ILAlgoTypes.Algos ILAlgoTypes.Algos_correct
         ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs
         ILAlgoTypes.PACK.applyTypes
         ILAlgoTypes.PACK.applyFuncs
         ILAlgoTypes.PACK.applyPreds

         ILAlgoTypes.BedrockPackage.bedrock_package
         Env.repr_combine Env.footprint Env.nil_Repr
         Env.listToRepr
         app map

         ILEnv.bedrock_funcs_r ILEnv.bedrock_types_r
         ILAlgoTypes.AllAlgos_composite
         ILAlgoTypes.oplus Prover.composite_ProverT
         (*TacPackIL.MEVAL.Composite.MemEvaluator_composite*) Env.listToRepr

         Plugin_PtsTo.ptsto32_ssig Bedrock.sep.Array.ssig cancel
CANCEL_TAC.canceller Provers.trivialProver SEP.typeof_preds types funcs preds
UNF.refineForward AssumptionProver.assumption_summary SEP.typeof_pred UNF.refineBackward
CANCEL_TAC.CANCEL.sepCancel SEP.WellTyped_sexpr CANCEL_TAC.CANCEL.cancel_in_order
CANCEL_TAC.CANCEL.order_impures CANCEL_TAC.SH_FACTS.sheapSubstU nsexprD
 CANCEL_TAC.CANCEL.unify_remove
 Folds.all2 is_well_typed CANCEL_TAC.CANCEL.unifyArgs ExprUnify.UNIFIER.Subst_empty
ExprUnify.UNIFIER.exprInstantiate
ExprUnify.UNIFIER.subst_empty
ExprUnify.UNIFIER.exprUnify
ExprUnify.UNIFIER.subst_exprInstantiate ExprUnify.UNIFIER.FM.empty CANCEL_TAC.existsSubst
CANCEL_TAC.existsMaybe CANCEL_TAC.substInEnv
CANCEL_TAC.CANCEL.meta_order_funcs
CANCEL_TAC.CANCEL.meta_order_args
CANCEL_TAC.CANCEL.exprs_count_meta
CANCEL_TAC.CANCEL.expr_count_meta
ExprUnify.UNIFIER.exprUnify_recursor
CANCEL_TAC.CANCEL.expr_size].

Ltac evaluate := evaluate_cbv.

Goal @cancel himp emp star ex inj types funcs preds nil nil
  (chainl (list_to 0 33))
  (chainr (list_to 0 33)).
cbv beta iota zeta delta [ chainl chainr list_to ].
Time (evaluate; reflexivity).
Time Qed.

Goal @cancel himp emp star ex inj types funcs preds nil nil
  (chainl (list_to 0 65))
  (chainr (list_to 0 65)).
cbv beta iota zeta delta [ chainl chainr list_to ].
Time (evaluate; reflexivity).
Time Qed.

Goal @cancel himp emp star ex inj types funcs preds nil nil
  (chainl (list_to 0 129))
  (chainr (list_to 0 129)).
cbv beta iota zeta delta [ chainl chainr list_to ].
Time (evaluate; reflexivity).
Time Qed.

Goal @cancel himp emp star ex inj types funcs preds nil nil
  (chainl (list_to 0 257))
  (chainr (list_to 0 257)).
cbv beta iota zeta delta [ chainl chainr list_to ].
Time (evaluate; reflexivity).
Time Qed.

Goal @cancel himp emp star ex inj types funcs preds nil nil
  (chainl (list_to 0 512))
  (chainr (list_to 0 512)).
cbv beta iota zeta delta [ chainl chainr list_to ].
Time (evaluate; reflexivity).
Time Qed.
