Require Import List Bool.
Require Import Expr SepExpr.
Require Import Reflection.
Require Import Folds.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable types : list type.
  Variable concl : Type.

  (** The type of one unfolding lemma *)
  Record lemma := 
  { Foralls : variables
    (* The lemma statement begins with this sequence of [forall] quantifiers over these types. *)
  ; Hyps : list (expr types)
    (* Next, we have this sequence of pure hypotheses. *)
  ; Concl : concl
  (* Finally, we have this separation implication, with lefthand and righthand sides. *)
  }.

  Variable WellTyped_concl : list tvar -> concl -> bool.

  Variable conclD : forall (meta_base var_base : env types), concl -> Prop.

  Definition WellTyped_lemma tfuncs (l : lemma) : bool :=
    allb (fun x => is_well_typed tfuncs nil (Foralls l) x tvProp) (Hyps l) &&
    WellTyped_concl (Foralls l) (Concl l).

  Variable funcs : functions types.

    (** Helper function to add a sequence of implications in front of a [Prop] *)
  Definition hypD (H : expr types) (meta_env var_env : env types) : Prop :=
    match exprD funcs meta_env var_env H tvProp with
      | None => False
      | Some P => P
    end.

  Fixpoint implyEach (Hs : list (expr types)) (meta_env var_env : env types) (P : Prop) : Prop :=
    match Hs with
      | nil => P
      | H :: Hs' => hypD H meta_env var_env -> implyEach Hs' meta_env var_env P
    end.

    (** The meaning of a lemma statement *)

    (* Redefine to use the opposite quantifier order *)
  Fixpoint forallEachR (ls : variables) : (env types -> Prop) -> Prop :=
    match ls with
      | nil => fun cc => cc nil
      | a :: b => fun cc =>
        forallEachR b (fun r => forall x : tvarD types a, cc (existT _ a x :: r))
    end.
    
  Definition lemmaD (meta_base var_base : env types) (lem : lemma) : Prop :=
    WellTyped_lemma (typeof_funcs funcs) lem = true /\
    forallEachR (Foralls lem) (fun env =>
      implyEach (Hyps lem) meta_base (var_base ++ env)
      (conclD meta_base (var_base ++ env) (Concl lem))).

  (** Lemmas **)
  Lemma forallEachR_sem : forall vs P,
    forallEachR vs P <-> (forall e, map (@projT1 _ _) e = vs -> P e).
  Proof.
    clear. split; revert P; induction vs; simpl; intros.
    destruct e; simpl in *; try congruence.
    destruct e; simpl in *; try congruence. inversion H0; clear H0; subst. eapply IHvs in H; eauto.
    destruct s; eapply H.
    eapply H; reflexivity.
    eapply IHvs; intros. eapply H. simpl. f_equal; auto.
  Qed.

  Lemma implyEach_instantiate : forall HYPS U G,
    AllProvable funcs U G HYPS ->
    forall cc,
      implyEach HYPS U G cc ->
      cc.
  Proof.
    induction HYPS; simpl; intros; auto;
      repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : _ && _ = _ |- _ ] => 
                 apply andb_true_iff in H; destruct H
             end.
    eapply IHHYPS; eauto.
  Qed. 

  Lemma implyEach_sem : forall cc U G es,
    implyEach es U G cc <-> (AllProvable funcs U G es -> cc).
  Proof. clear; induction es; simpl; intuition. Qed.

End typed.

Module Type SepLemmaType (SE : SepExpr).

  Section typed.
    Variable types : list type.
    
    Definition sepConcl : Type :=
      (SE.sexpr types * SE.sexpr types)%type.

    Definition Lhs (l : lemma types sepConcl) : SE.sexpr types :=
      fst (Concl l).
    Definition Rhs (l : lemma types sepConcl) : SE.sexpr types :=
      snd (Concl l).
    
    Definition WellTyped_sepConcl tfuncs tpreds (vars : list tvar) (c : sepConcl) : bool :=
      if SE.WellTyped_sexpr tfuncs tpreds nil vars (fst c)
      then 
        SE.WellTyped_sexpr tfuncs tpreds nil vars (snd c)
      else false.

    Definition sepConclD funcs preds (uvars vars : env types) (c : sepConcl) : Prop :=
      SE.himp funcs preds uvars vars (fst c) (snd c).

    Definition sepLemma : Type := lemma types sepConcl.

    Definition WellTyped_sepLemma tfuncs tpreds (l : sepLemma) : bool :=
      WellTyped_lemma (WellTyped_sepConcl tfuncs tpreds) tfuncs l.

    Definition sepLemmaD (funcs : functions types) (preds : SE.predicates types) 
      (meta_base var_base : env types) (lem : sepLemma) : Prop :=
      lemmaD (WellTyped_sepConcl (typeof_funcs funcs) (SE.typeof_preds preds)) 
             (sepConclD funcs preds) funcs meta_base var_base lem.
  End typed.

End SepLemmaType.

Module SepLemma (SE : SepExpr) <: SepLemmaType SE.

  Section typed.
    Variable types : list type.
    
    Definition sepConcl : Type :=
      (SE.sexpr types * SE.sexpr types)%type.

    Definition Lhs (l : lemma types sepConcl) : SE.sexpr types :=
      fst (Concl l).
    Definition Rhs (l : lemma types sepConcl) : SE.sexpr types :=
      snd (Concl l).
    
    Definition WellTyped_sepConcl tfuncs tpreds (vars : list tvar) (c : sepConcl) : bool :=
      if SE.WellTyped_sexpr tfuncs tpreds nil vars (fst c)
      then 
        SE.WellTyped_sexpr tfuncs tpreds nil vars (snd c)
      else false.

    Definition sepConclD funcs preds (uvars vars : env types) (c : sepConcl) : Prop :=
      SE.himp funcs preds uvars vars (fst c) (snd c).

    Definition sepLemma : Type := lemma types sepConcl.

    Definition WellTyped_sepLemma tfuncs tpreds (l : sepLemma) : bool :=
      WellTyped_lemma (WellTyped_sepConcl tfuncs tpreds) tfuncs l.

    Definition sepLemmaD (funcs : functions types) (preds : SE.predicates types) 
      (meta_base var_base : env types) (lem : sepLemma) : Prop :=
      lemmaD (WellTyped_sepConcl (typeof_funcs funcs) (SE.typeof_preds preds)) 
             (sepConclD funcs preds) funcs meta_base var_base lem.
  End typed.

End SepLemma.