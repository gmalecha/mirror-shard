Require Import List.
Require Import SepTheory.
Require Import RelationClasses.
Require Import Expr ExprUnify.
Require Import SepExpr SepHeap.
Require Import Setoid.
Require Import Prover.
Require Import SepExpr.
Require Import Folds.
Require Import Tactics.
Require Import Instantiation.
Require Ordering.
Require SepUnify.

Set Implicit Arguments.
Set Strict Implicit.

Module Type Canceller (SUBST : Subst)
                      (ST : SepTheory.SepTheory)
                      (SE : SepExpr ST)
                      (SH : SepHeap ST SE).

  Section typed.
    Variable types : list type.
    Variable funcs : functions types.
    Variable preds : SE.predicates types.
    Variable prover : ProverT types.

    (** NOTE: return None if we don't make progress
     **)
    Parameter sepCancel : forall (bound : nat) (tpreds : SE.tpredicates)
      (facts : Facts (types := types) prover) 
      (l r : SH.SHeap types) (s : SUBST.Subst types),
      option (SH.SHeap types * SH.SHeap types * SUBST.Subst types).

    Variable PC : ProverT_correct prover funcs.

    Axiom sepCancel_correct : forall U G bound facts l r l' r' sub sub',
      SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub' ->
      SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env U) (typeof_env G) l = true ->
      SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env U) (typeof_env G) r = true ->
      Valid PC U G facts ->
      sepCancel bound (SE.typeof_preds preds) facts l r sub' = Some (l', r', sub) ->
      SE.himp funcs preds U G (SH.sheapD l') (SH.sheapD r') ->
      SUBST.Subst_equations funcs U G sub ->
      SE.himp funcs preds U G (SH.sheapD l) (SH.sheapD r).

    Axiom sepCancel_PuresPrem : forall tp U G bound facts l r l' r' s s',
      sepCancel bound tp facts l r s = Some (l', r', s') ->
      AllProvable funcs U G (SH.pures l) ->
      AllProvable funcs U G (SH.pures l').

    Axiom sepCancel_PureFacts : forall tU tG bound facts l r l' r' s s',
      let tf := typeof_funcs funcs in
      let tp := SE.typeof_preds preds in
      sepCancel bound tp facts l r s = Some (l', r', s') ->
      SUBST.Subst_WellTyped tf tU tG s ->
      SH.WellTyped_sheap tf tp tU tG l = true ->
      SH.WellTyped_sheap tf tp tU tG r = true ->
         SUBST.Subst_WellTyped tf tU tG s' 
      /\ SH.WellTyped_sheap tf tp tU tG l' = true
      /\ SH.WellTyped_sheap tf tp tU tG r' = true
      /\ SUBST.Subst_Extends s' s.

  End typed.
  
End Canceller.

