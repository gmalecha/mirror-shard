Require Import Coq.Lists.List.
Require Import Expr.
Require Import ExtLib.Core.EquivDec.
Require Import ExtLib.Tactics.Consider.
Require Import Instantiation.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (S : Subst).

  Section parametric.
    Variable ts : list type.

    Definition rawSubst : Type :=
      list (option (expr ts)).

    Definition rawSubst_lookup (rs : rawSubst) (u : uvar) : option (expr ts) :=
      match nth_error rs u with
        | Some x => x
        | None => None
      end.

    Fixpoint list_set_nth {T} (ls : list (option T)) (n : nat) (x : T) : list (option T) :=
      match n with
        | 0 => Some x :: tl ls
        | S n => hd None ls :: list_set_nth (tl ls) n x
      end.

    Definition from_subst (s : S.Subst ts) : rawSubst :=
      List.fold_left (fun acc u =>
                        match S.Subst_lookup u s with
                          | None => acc
                          | Some val => list_set_nth acc u val
                        end) (S.Subst_domain s) nil.

    Lemma rawSubst_lookup_list_set_nth_eq
    : forall u e acc, rawSubst_lookup (list_set_nth acc u e) u = Some e.
    Proof.
      induction u; simpl; intros.
      { unfold rawSubst_lookup. reflexivity. }
      { unfold rawSubst_lookup. simpl.
        erewrite <- IHu. reflexivity. }
    Qed.

    Lemma rawSubst_lookup_list_set_nth_neq
    : forall e u u' acc,
        u <> u' ->
        rawSubst_lookup (list_set_nth acc u e) u' = rawSubst_lookup acc u'.
    Proof.
      induction u; simpl; intros.
      { destruct u'.
        { exfalso; auto. }
        { unfold rawSubst_lookup. simpl. destruct acc; simpl.
          { destruct u'; reflexivity. }
          { reflexivity. } } }
      { destruct u'.
        { unfold rawSubst_lookup. simpl.
          destruct acc; reflexivity. }
        { assert (u <> u') by omega. specialize (IHu u' (tl acc) H0).
          unfold rawSubst_lookup in *; simpl in *.
          rewrite IHu. destruct acc; simpl.
          destruct u'; reflexivity.
          reflexivity. } }
    Qed.

    Lemma rawSubst_lookup_from_subst_Some
    : forall (s : S.Subst ts) (u : uvar) ls acc x,
        rawSubst_lookup
          (fold_left
             (fun (acc : list (option (expr ts))) (u0 : uvar) =>
                match S.Subst_lookup u0 s with
                  | Some val => list_set_nth acc u0 val
                  | None => acc
                end) ls acc) u = Some x ->
        ((In u ls /\ S.Subst_lookup u s = Some x) \/
         rawSubst_lookup acc u = Some x).
    Proof.
      induction ls; simpl; intros.
      { intuition. }
      { eapply IHls in H.
        intuition.
        { Require Import ExtLib.Tactics.
          Require Import ExtLib.Core.RelDec.
          forward.
          consider (a ?[ eq ] u); intros; subst.
          { left. split; auto. rewrite rawSubst_lookup_list_set_nth_eq in H0.
            inversion H0; clear H0; subst. assumption. }
          { right. rewrite rawSubst_lookup_list_set_nth_neq in H0; eauto. } } }
    Qed.

    Lemma rawSubst_lookup_from_subst_None
    : forall (s : S.Subst ts) (u : uvar) ls acc,
        rawSubst_lookup
          (fold_left
             (fun (acc : list (option (expr ts))) (u0 : uvar) =>
                match S.Subst_lookup u0 s with
                  | Some val => list_set_nth acc u0 val
                  | None => acc
                end) ls acc) u = None ->
        ((In u ls -> S.Subst_lookup u s = None) /\
         rawSubst_lookup acc u = None).
    Proof.
      induction ls; simpl; intros.
      { intuition. }
      { eapply IHls in H.
        consider (S.Subst_lookup a s); intros.
        { intuition; subst.
          { rewrite rawSubst_lookup_list_set_nth_eq in H2. congruence. }
          { consider (a ?[ eq ] u); intros; subst.
            { rewrite rawSubst_lookup_list_set_nth_eq in H2. congruence. }
            { rewrite rawSubst_lookup_list_set_nth_neq in H2; eauto. } } }
        { intuition; subst; auto. } }
    Qed.

    Theorem rawSubst_lookup_from_subst
    : forall s u,
        rawSubst_lookup (from_subst s) u = S.Subst_lookup u s.
    Proof.
      intros. unfold from_subst.
      consider (rawSubst_lookup
                  (fold_left
                     (fun (acc : list (option (expr ts))) (u0 : uvar) =>
                        match S.Subst_lookup u0 s with
                          | Some val => list_set_nth acc u0 val
                          | None => acc
                        end) (S.Subst_domain s) nil) u).
      { intros. eapply rawSubst_lookup_from_subst_Some in H.
        destruct H. intuition.
        unfold rawSubst_lookup in H; destruct u; simpl in H; congruence. }
      { intros. eapply rawSubst_lookup_from_subst_None in H.
        intuition.
        consider (S.Subst_lookup u s); intros; auto.
        symmetry. apply H0.
        eapply S.Subst_domain_iff. eauto. }
    Qed.

  End parametric.

End Make.