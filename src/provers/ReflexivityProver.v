Require Import List DepList.
Require Import Expr Env.
Require Import Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Reflexivity Prover **)

Section ReflexivityProver.
  Context {types : list type}.
  Variable fs : functions types.
  
  Definition reflexivityValid (_ _ : env types) (_ : unit) := True.

  Definition reflexivitySummarize (_ : hlist Pkg types) (_ : list (expr types)) := tt.

  Definition reflexivityProve (types_eq : hlist Pkg types) (_ : unit) (goal : expr types) := 
    match goal with
      | Equal _ x y => if expr_seq_dec types_eq x y then true else false
      | _ => false
    end.

  Definition reflexivityLearn (types_eq : hlist Pkg types) (sum : unit) (hyps : list (expr types)) := sum.

  Lemma reflexivitySummarizeCorrect : forall types_eq uvars vars hyps,
    AllProvable fs uvars vars hyps ->
    reflexivityValid uvars vars (reflexivitySummarize types_eq hyps).
  Proof.
    unfold reflexivityValid; auto.
  Qed.

  Lemma reflexivityLearnCorrect : forall teq uvars vars sum,
    reflexivityValid uvars vars sum -> forall hyps, 
    AllProvable fs uvars vars hyps ->
    reflexivityValid uvars vars (reflexivityLearn teq sum hyps).
  Proof.
    unfold reflexivityValid; auto.
  Qed.

  Theorem reflexivityProverCorrect : ProverCorrect fs reflexivityValid reflexivityProve.
    unfold reflexivityProve; t.
  Qed.

  Definition reflexivityProver : ProverT types :=
  {| Facts := unit
   ; Summarize := reflexivitySummarize
   ; Learn := reflexivityLearn
   ; Prove := reflexivityProve
   |}.
  Definition reflexivityProver_correct : ProverT_correct reflexivityProver fs.
  eapply Build_ProverT_correct with (Valid := reflexivityValid);
    eauto using reflexivitySummarizeCorrect, reflexivityLearnCorrect, reflexivityProverCorrect.
  Qed.

End ReflexivityProver.

Definition ReflexivityProver : ProverPackage :=
{| ProverTypes := nil_Repr (Empty_set : Type)
 ; ProverFuncs := fun ts => nil_Repr (Default_signature ts)
 ; Prover_correct := fun ts fs => reflexivityProver_correct fs
|}.

Ltac unfold_reflexivityProver H :=
  match H with
    | tt =>
      cbv delta [
        reflexivityProver
        reflexivitySummarize reflexivityLearn reflexivityProve
        expr_seq_dec 
      ]
    | _ =>
      cbv delta [
        reflexivityProver
        reflexivitySummarize reflexivityLearn reflexivityProve
        expr_seq_dec 
      ] in H        
  end.
