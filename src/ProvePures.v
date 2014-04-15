Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorShard.Prover.
Require Import MirrorShard.Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section prover.
  Variable ts : list type.
  Variable fs : functions ts.
  Variable prover : ProverT ts.

  Fixpoint provePures (facts : Facts prover) (ls : exprs ts) : exprs ts :=
    match ls with
      | nil => nil
      | l :: ls =>
        let ls' := provePures (Learn _ facts (l :: nil)) ls in
        if Prove _ facts l then ls'
        else l :: ls'
    end.

  Variable proverOk : ProverT_correct prover fs.

  Theorem provePuresOk : forall u g ls f ls',
    Valid proverOk u g f  ->
    Forall (ValidProp fs u g) ls ->
    provePures f ls = ls' ->
    AllProvable fs u g ls' ->
    AllProvable fs u g ls.
  Proof.
    induction ls; simpl; intros; auto.
    { inversion H0; clear H0; subst.
      consider (Prove prover f a).
      { intuition.
        { eapply ProverCorrect_ProverCorrect'.
          eapply Prove_correct; eauto.
          eauto. eauto. eauto. }
        { eapply IHls; [ | | reflexivity | eassumption ].
          eapply Learn_correct; eauto. repeat constructor.
          eapply ProverCorrect_ProverCorrect'.
          eapply Prove_correct; eauto. eauto. eauto. eauto.
          eauto. } }
      { intros. inversion H1; clear H1; subst.
        intuition. eapply IHls; [ | | reflexivity | eassumption ]; eauto.
        eapply Learn_correct; eauto. repeat constructor; auto. } }
  Qed.
End prover.
