Require Import List.
Require Import Expr.
Require Import ExtLib.Core.EquivDec.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.

Module Type Subst.
  (** An environment that maintains a mapping from variables to their meaning **)
  Parameter Subst : list type -> Type.

  Section typed.
    Variable types : list type.
    
    (** Predicates **)
    Parameter Subst_WellTyped : tfunctions -> tenv -> tenv -> Subst types -> Prop.

    (** Relations **)
    Parameter Subst_Equal : Subst types -> Subst types -> Prop.
    Parameter Equiv_Subst_Equal : RelationClasses.Equivalence Subst_Equal.

    Parameter Subst_Extends : Subst types -> Subst types -> Prop.

    Parameter Refl_Subst_Extends : RelationClasses.Reflexive Subst_Extends.
    Parameter Antisym_Subst_Extends : @RelationClasses.Antisymmetric _ _ Equiv_Subst_Equal Subst_Extends.
    Parameter Trans_Subst_Extends : RelationClasses.Transitive Subst_Extends.

    (** Operations **)
    Parameter Subst_empty : Subst types.

    Axiom Subst_empty_WellTyped : forall funcs U G,
      Subst_WellTyped funcs U G Subst_empty.

    Parameter Subst_lookup : uvar -> Subst types -> option (expr types).
    Parameter Subst_set : uvar -> expr types -> Subst types -> option (Subst types).

    Parameter Subst_size : Subst types -> nat.
    Parameter Subst_domain : Subst types -> list uvar.
   
    (** Substitute meta variables **)
    Parameter exprInstantiate : Subst types -> expr types -> expr types.

    Axiom exprInstantiate_WellTyped : forall funcs U G sub,
      Subst_WellTyped funcs U G sub ->
      forall e t, 
        is_well_typed funcs U G e t = is_well_typed funcs U G (exprInstantiate sub e) t.
    
    Axiom exprInstantiate_Extends : forall x y,
      Subst_Extends x y ->
      forall t, exprInstantiate x (exprInstantiate y t) = exprInstantiate x t.

    Axiom exprInstantiate_extends : forall sub sub' l r,
      exprInstantiate sub l = exprInstantiate sub r ->
      Subst_Extends sub' sub -> 
      exprInstantiate sub' l = exprInstantiate sub' r.

    Axiom exprInstantiate_instantiated : forall k sub e,
      Subst_lookup k sub = Some e ->
      exprInstantiate sub e = e.

    Axiom exprInstantiate_Removes : forall k sub e e' e'',
      Subst_lookup k sub = Some e ->
      exprInstantiate sub e' = e'' ->
      mentionsU k e'' = false.

    (** The meaning of size **)
    Axiom Subst_domain_iff : forall s k,
      (exists e, Subst_lookup k s = Some e) <-> In k (Subst_domain s).

    Axiom Subst_size_cardinal : forall sub,
      Subst_size sub = length (Subst_domain sub).

    (** Axiomatization of exprInstantiate **)
    Axiom exprInstantiate_Func : forall a b c,
      exprInstantiate a (Func b c) = Func b (map (exprInstantiate a) c).

    Axiom exprInstantiate_Equal : forall a b c d,
      exprInstantiate a (Equal b c d) = Equal b (exprInstantiate a c) (exprInstantiate a d).

    Axiom exprInstantiate_Not : forall a b,
      exprInstantiate a (Not b) = Not (exprInstantiate a b).

    Axiom exprInstantiate_UVar : forall a x,
      exprInstantiate a (UVar x) = match Subst_lookup x a with
                                     | None => UVar x
                                     | Some v => v
                                   end.

    Axiom exprInstantiate_Var : forall a x, 
      exprInstantiate a (Var x) = Var x.

    Axiom exprInstantiate_Const : forall a t v, 
      exprInstantiate a (@Const types t v) = (@Const types t v).

    (** Subst_set & Subst_lookup **)
    Axiom Subst_set_Subst_lookup : forall k v sub sub',
      Subst_set k v sub = Some sub' ->
      Subst_lookup k sub' = Some (exprInstantiate sub v).

    Axiom Subst_set_Extends : forall k v sub sub',
      Subst_set k v sub = Some sub' ->
      Subst_lookup k sub = None ->
      Subst_Extends sub' sub.

    Axiom Subst_lookup_Extends : forall sub sub' k v,
      Subst_lookup k sub = Some v ->
      Subst_Extends sub' sub ->
      Subst_lookup k sub' = Some (exprInstantiate sub' v).

    Axiom Subst_set_exprInstantiate : forall x e sub sub',
      Subst_set x e sub = Some sub' ->
      Subst_lookup x sub = None -> 
      exprInstantiate sub' (UVar x) = exprInstantiate sub' e.

    Axiom Subst_set_WellTyped : forall funcs U G u E t sub sub',
      Subst_set u E sub = Some sub' ->
      nth_error U u = Some t ->
      is_well_typed funcs U G E t = true ->
      Subst_WellTyped funcs U G sub ->
      Subst_WellTyped funcs U G sub'.


    (** Well-typedness **)
    Axiom WellTyped_lookup : forall funcs U G sub,
      Subst_WellTyped funcs U G sub ->
      forall u e,
      Subst_lookup u sub = Some e ->
      exists t, nth_error U u = Some t /\
      is_well_typed funcs U G e t = true.

    (** Semantics interpretation of substitutions **)
    Parameter Subst_equations : 
      forall (funcs : functions types) (U G : env types), Subst types -> Prop.

    Axiom Subst_equations_empty : forall funcs U G,
      Subst_equations funcs U G Subst_empty.

    Axiom Subst_equations_weaken : forall funcs U G s U' G',
      Subst_equations funcs U G s ->
      Subst_equations funcs (U ++ U') (G ++ G') s.

    Axiom Subst_equations_exprInstantiate : forall funcs U G e t sub,
      Subst_equations funcs U G sub ->
      exprD funcs U G (exprInstantiate sub e) t = exprD funcs U G e t.

    Axiom Subst_equations_Extends : forall funcs G sub sub' U,
      Subst_Extends sub' sub ->
      Subst_equations funcs U G sub' ->
      Subst_equations funcs U G sub.

    Axiom Subst_equations_WellTyped : forall funcs G U sub,
      Subst_equations funcs U G sub ->
      Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub.

    (** An incremental version of Subst_equations **)
    Section Subst_equations_to.
      Variable funcs : functions types. 
      Variables uenv venv : env types.
      Variable subst : Subst types.

      Fixpoint Subst_equations_to (from : nat) (ls : Expr.env types) : Prop :=
        match ls with
          | nil => True
          | l :: ls =>
            match Subst_lookup from subst with
              | None => True
              | Some e => match exprD funcs uenv venv e (projT1 l) with
                            | None => False
                            | Some v => projT2 l = v
                          end
            end /\ Subst_equations_to (S from) ls 
        end.

      Axiom Subst_equations_to_Subst_equations : 
        Subst_WellTyped (typeof_funcs funcs) (typeof_env uenv) (typeof_env venv) subst ->
        Subst_equations_to 0 uenv ->
        Subst_equations funcs uenv venv subst.

    End Subst_equations_to.
        
  End typed.

End Subst.

Module SubstFacts (S : Subst).

  Section typed.
    Variable types : list type.
    Variable funcs : functions types.

    Theorem Subst_equations_to_app : forall m v s vs from vs',
      S.Subst_equations_to funcs m v s from (vs ++ vs') <->
      (S.Subst_equations_to funcs m v s from vs /\
        S.Subst_equations_to funcs m v s (from + length vs) vs').
    Proof.
      clear. induction vs; simpl; intros.
      { rewrite Plus.plus_0_r. intuition. }
      { rewrite IHvs. rewrite <- Plus.plus_Snm_nSm. simpl. 
        intuition. }
    Qed.

    Theorem Subst_equations_to_weaken : forall m v s vs from,
      S.Subst_equations_to funcs m v s from vs ->
      forall m' v',
        S.Subst_equations_to funcs (m ++ m') (v ++ v') s from vs.
    Proof.
      clear. induction vs; simpl in *; intros; auto.
      { intuition. destruct (S.Subst_lookup from s); auto.
        consider (exprD funcs m v e (projT1 a)); intros.
        erewrite exprD_weaken; eauto. contradiction. }
    Qed.
  End typed.

End SubstFacts.
