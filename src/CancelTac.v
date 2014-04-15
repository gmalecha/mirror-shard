Require Import Coq.Lists.List.
Require Import MirrorShard.Expr MirrorShard.SepExpr.
Require Import MirrorShard.SepHeap MirrorShard.SepCancel.
Require Import MirrorShard.Prover.
Require Import MirrorShard.Tactics MirrorShard.Reflection.
Require MirrorShard.ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Module CancellerTac (ST : SepTheory.SepTheory)
                    (SE : SepExpr ST)
                    (SH : SepHeap ST SE)
                    (C : Canceller ST SE SH).
  Module SH_FACTS := SepHeap.SepHeapFacts ST SE SH.

Section existsSubst.
  Variable types : list type.
  Variable funcs : functions types.
  Variable meta_base : env types.
  Variable var_env : env types.
  Variable sub : C.U.Subst types.

  Definition ExistsSubstNone (_ : tvar) (_ : expr types) :=
    False.

  Fixpoint substInEnv (from : nat) (vals : env types) (ret : env types -> Prop) : Prop :=
    match vals with
      | nil => ret nil
      | val :: vals =>
        match C.U.Subst_lookup from sub with
          | None => substInEnv (S from) vals (fun e => ret (val :: e))
          | Some v =>
            match exprD funcs meta_base var_env v (projT1 val) with
              | None => ExistsSubstNone (projT1 val) v
              | Some v' => projT2 val = v' /\ substInEnv (S from) vals (fun e => ret (existT _ (projT1 val) v' :: e))
            end
        end
    end.

  Fixpoint existsMaybe (vals : list { t : tvar & option (tvarD types t) }) (ret : env types -> Prop) : Prop :=
    match vals with
      | nil => ret nil
      | existT t None :: vals => exists x : tvarD types t, existsMaybe vals (fun e => ret (existT _ t x :: e))
      | existT t (Some v) :: vals => existsMaybe vals (fun e => ret (existT _ t v :: e))
    end.

End existsSubst.

Definition existsSubst types funcs var_env sub (from : nat) (vals : list { t : tvar & option (tvarD types t) }) (ret : env types -> Prop) :=
  existsMaybe vals (fun e => @substInEnv types funcs e var_env sub from e ret).

Fixpoint consistent {ts} (vals : list { x : tvar & option (tvarD ts x) }) (e : list { x : tvar & tvarD ts x }) : Prop :=
  match vals , e with
    | nil , nil => True
    | existT t None :: vals , existT t' _ :: e =>
      t = t' /\ @consistent _ vals e
    | existT t (Some v) :: vals , existT t' v' :: e =>
      match equiv_dec t t' return Prop with
        | left pf =>
          v' = match (pf : t = t') in _ = t return tvarD ts t with
                 | refl_equal => v
               end /\ @consistent _ vals e
        | right _ => False
      end
    | _ , _ => False
  end.

Lemma ex_iff : forall T (P P' : T -> Prop),
  (forall x, P x <-> P' x) ->
  ((exists x, P x) <-> (exists x, P' x)).
Proof. split; intuition; destruct H0 as [ x ? ]; exists x; firstorder. Qed.

Theorem existsMaybe_sem : forall types vals (ret : env types -> Prop),
  existsMaybe vals ret <->
  existsEach (map (@projT1 _ _) vals) (fun e => consistent vals e /\ ret e).
Proof.
  induction vals; simpl; intros.
  { intuition. }
  { destruct a. destruct o.
    { rewrite IHvals. intuition. exists t. apply existsEach_sem. apply existsEach_sem in H.
      destruct H. exists x0. simpl in *. rewrite EquivDec_refl_left. intuition.
      destruct H. apply existsEach_sem. apply existsEach_sem in H. destruct H.
      exists x1. simpl in *. rewrite EquivDec_refl_left in H. intuition; subst; auto. }
    { simpl. eapply ex_iff. intros. rewrite IHvals.
      intuition; apply existsEach_sem in H; apply existsEach_sem; destruct H; exists x1; intuition. } }
Qed.

Lemma substInEnv_sem : forall types funcs meta_env var_env sub vals from ret,
  @substInEnv types funcs meta_env var_env sub from vals ret <->
  (C.U.Subst_equations_to funcs meta_env var_env sub from vals /\ ret vals).
Proof.
  induction vals; simpl; intros.
  { intuition. }
  { destruct a; simpl in *.
    consider (C.U.Subst_lookup from sub); simpl; intros.
    consider (exprD funcs meta_env var_env e x); simpl; intros.
    { rewrite IHvals. intuition; subst; auto. }
    { intuition. }
    { rewrite IHvals. intuition. } }
Qed.

Lemma existsSubst_sem : forall ts (funcs : functions ts) vals sub vars_env from ret,
  existsSubst funcs vars_env sub from vals ret <->
  existsEach (map (@projT1 _ _) vals) (fun meta_env =>
    consistent vals meta_env /\ C.U.Subst_equations_to funcs meta_env vars_env sub from meta_env /\ ret meta_env).
Proof.
  intros. unfold existsSubst.
  rewrite existsMaybe_sem. rewrite existsEach_sem. rewrite existsEach_sem.
  apply ex_iff. intros. rewrite substInEnv_sem. intuition.
Qed.

(** The actual canceller starts here **)
Section canceller.
  Variable types : list type.
  Variable funcs : functions types.
  Variable preds : SE.predicates types.
  Variable prover : ProverT types.

  Record CancellerResult : Type :=
  { Lhs    : SH.SHeap types
  ; Rhs    : SH.SHeap types
  ; Subst  : C.U.Subst types
  }.

  Let bound := 10.

  Definition canceller tpreds (facts : Facts prover)
    (lhs rhs : SH.SHeap types) (sub : C.U.Subst types) : CancellerResult * bool :=
    match C.sepCancel prover bound tpreds facts lhs rhs sub with
      | Some (l,r,s) =>
        ({| Lhs := l ; Rhs := r ; Subst := s |}, true)
      | None =>
        ({| Lhs := lhs ; Rhs := rhs ; Subst := sub |}, false)
    end.

  Lemma WellTyped_env_app : forall ts a b c d,
    WellTyped_env a c ->
    WellTyped_env b d ->
    WellTyped_env (types := ts) (a ++ b) (c ++ d).
  Proof. clear.
    intros. unfold WellTyped_env in *. unfold typeof_env in *. subst.
    rewrite map_app. reflexivity.
  Qed.
  Ltac t_list_length := repeat (rewrite typeof_env_length || rewrite rev_length || rewrite map_length || rewrite app_length).
  Hint Extern 1 (_ = _) => t_list_length; auto : list_length.

  Ltac env_resolution :=
    repeat (rewrite typeof_env_app || unfold typeof_env || rewrite map_app || rewrite map_rev || (f_equal; []) || assumption).

  Lemma consistent_app : forall ts a b c,
    consistent (ts := ts) (a ++ b) c ->
    consistent a (firstn (length a) c) /\ consistent b (skipn (length a) c).
  Proof. clear.
    induction a; simpl; intros; auto.
    destruct a. destruct o. destruct c; try contradiction. destruct s. destruct (equiv_dec x x0); try contradiction.
    destruct H. eapply IHa in H0. intuition.
    destruct c; try contradiction. destruct s. destruct H. apply IHa in H0. intuition.
  Qed.
  Lemma consistent_Some : forall ts a c,
    consistent (ts := ts) (map (fun x => existT _ (projT1 x) (Some (projT2 x))) a) c <->
    a = c.
  Proof.
    induction a; destruct c; simpl; intros; try contradiction; intuition auto; try congruence.
    { destruct s. destruct a; simpl in *. destruct (equiv_dec x0 x); try contradiction.
      unfold equiv in e. intuition; subst. f_equal; eauto. eapply IHa; eauto. }
    { inversion H; clear H; subst. destruct s. simpl in *.
      destruct (equiv_dec x x); unfold equiv in *; eauto.
      intuition eauto. 2: eapply IHa; eauto. clear.
      rewrite EqdepClass.UIP_refl with (p1 := e). reflexivity. }
  Qed.

  Lemma ApplyCancelSep_with_eq' : forall (PC : ProverT_correct prover funcs) (meta_env var_env : env types)
    (facts : Facts prover) (sub : C.U.Subst _),
    Valid PC meta_env var_env facts ->
    C.U.Subst_equations funcs meta_env var_env sub ->
    forall (l r : SH.SHeap types) res prog,
    forall (WTR : SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) (typeof_env var_env) r = true),
    forall (WTL : SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) (typeof_env var_env) l = true),
    canceller (SE.typeof_preds preds) facts l r sub = (res, prog) ->
    match res with
      | {| Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
      C.U.Subst_Extends subst sub ->
      SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) (typeof_env var_env) lhs' = true ->
      SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) (typeof_env var_env) rhs' = true ->
        existsSubst funcs var_env subst 0
          (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env)
          (fun meta_env : Expr.env types =>
            ST.himp
              (SE.sexprD funcs preds meta_env var_env (SH.sheapD lhs'))
              (SE.sexprD funcs preds meta_env var_env (SH.sheapD rhs')))

    end ->
    ST.himp (@SE.sexprD _ funcs preds meta_env var_env (SH.sheapD l))
                    (@SE.sexprD _ funcs preds meta_env var_env (SH.sheapD r)).
  Proof.
    Opaque Env.repr.
    intros. unfold canceller in *.

    consider (C.sepCancel prover bound (SE.typeof_preds preds) facts l r sub); intros.
    { destruct p. destruct p. inversion H3; clear H3; subst.
      generalize H1. simpl in *. intros;  eapply C.sepCancel_PureFacts in H1; intuition eauto.

      specialize (H6 H1 H5).
      eapply SH_FACTS.SEP_FACTS.himp_WellTyped_sexpr; intros.
      eapply existsSubst_sem in H6.
      rewrite map_map in *. simpl in *.
      eapply existsEach_sem in H6. destruct H6. intuition.
      eapply consistent_Some in H6; subst.

      eapply C.sepCancel_correct in H3; try eassumption.
      eapply C.U.Subst_equations_WellTyped; eassumption.

      eapply C.U.Subst_equations_to_Subst_equations; eauto.
      eapply C.sepCancel_PureFacts in H1; try eassumption; intuition.
      eapply C.U.Subst_equations_WellTyped; eassumption.
      eapply C.U.Subst_equations_WellTyped; eassumption. }
    { inversion H3; clear H3; subst.
      simpl in *. intuition.
      eapply SH_FACTS.himp_pull_pures; intros.
      eapply existsSubst_sem in H2.
      rewrite map_map in H2. simpl in H2.
      eapply existsEach_sem in H2.
      destruct H2. intuition.
      eapply consistent_Some in H2; subst. eauto.
      reflexivity. eauto. eauto. }
  Qed.

  Theorem canceller_PuresPrem : forall tp U G bound s l r cr b,
      canceller bound tp l r s = (cr, b) ->
      AllProvable funcs U G (SH.pures l) ->
      AllProvable funcs U G (SH.pures (Lhs cr)).
  Proof.
    clear; unfold canceller; simpl in *; intros.
    consider (C.sepCancel prover bound bound0 tp l r s); intros.
    destruct p; destruct p. inversion H1; clear H1; subst.
    eapply C.sepCancel_PuresPrem. 2: eassumption. eassumption.
    inversion H1; clear H1; subst; simpl. eassumption.
  Qed.

  (** Shouldn't be necessary any more **)
  Theorem canceller_PureFacts : forall tU tG facts l r s cr b,
      let tf := typeof_funcs funcs in
      let tp := SE.typeof_preds preds in
      canceller tp facts l r s = (cr,b) ->
      C.U.Subst_WellTyped tf tU tG s ->
      SH.WellTyped_sheap tf tp tU tG l = true ->
      SH.WellTyped_sheap tf tp tU tG r = true ->
         C.U.Subst_WellTyped (types := types) tf tU tG (Subst cr)
      /\ SH.WellTyped_sheap (types := types) tf tp tU tG (Lhs cr) = true
      /\ SH.WellTyped_sheap (types := types) tf tp tU tG (Rhs cr) = true.
  Proof.
    clear. unfold canceller; simpl in *; intros.
    consider (C.sepCancel prover bound (SE.typeof_preds preds) facts l r s); intros.
    destruct p. destruct p. inversion H3; clear H3; subst.
    eapply C.sepCancel_PureFacts in H; intuition eauto.
    inversion H3; clear H3; subst; auto.
  Qed.

End canceller.

End CancellerTac.