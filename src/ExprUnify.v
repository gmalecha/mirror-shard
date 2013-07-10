Require Import Expr.
Require Import Instantiation.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SemanticUnifier (S : Subst).
  Section typed.
    Variable types : list type.

    (** The actual unification algorithm **)
    Parameter exprUnify : nat -> expr -> expr -> S.Subst -> option S.Subst.

    (** This is the soundness statement. **)
    Axiom exprUnify_sound_sem : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
      exprD (types := types) funcs U G (S.exprInstantiate sub' l) t = 
      exprD funcs U G (S.exprInstantiate sub' r) t.

    Axiom exprUnify_Extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.Subst_Extends sub' sub.

    Axiom exprUnify_WellTyped : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
        is_well_typed funcs U G l t = true ->
        is_well_typed funcs U G r t = true ->
        S.Subst_WellTyped funcs U G sub ->
        S.Subst_WellTyped funcs U G sub'.
        
  End typed.
End SemanticUnifier.

Module Type SyntacticUnifier (S : Subst).
  Include (SemanticUnifier S).

  Section typed.
    Variable types : list type.

    (** This is the soundness statement. **)
    Axiom exprUnify_sound_syn : forall n l r sub sub',
      @exprUnify n l r sub = Some sub' ->
      S.exprInstantiate sub' l = S.exprInstantiate sub' r.
       
  End typed.
End SyntacticUnifier.

Module SyntacticKernel (S : Subst).
  Section typed.
    Variable types : list type.

    (** The actual unification algorithm **)
    Parameter exprUnify : nat -> expr -> expr -> S.Subst -> option S.Subst.

    (** This is the soundness statement. **)
    Axiom exprUnify_sound_syn : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.exprInstantiate sub' l = S.exprInstantiate sub' r.

    Axiom exprUnify_Extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.Subst_Extends sub' sub.

    Axiom exprUnify_WellTyped : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
        is_well_typed funcs U G l t = true ->
        is_well_typed funcs U G r t = true ->
        S.Subst_WellTyped funcs U G sub ->
        S.Subst_WellTyped funcs U G sub'.
        
  End typed.
End SyntacticKernel.
