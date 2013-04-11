Require Import Expr.
Require Import Prover.
Require Import provers.ReflexivityProver.
Require Import provers.AssumptionProver.

Set Implicit Arguments.
Set Strict Implicit.

Section typed.
  Variable ts : list type.
  
  Definition trivialProver : ProverT ts :=
    composite_ProverT (@reflexivityProver ts) (assumptionProver ts).

  Variable fs : functions ts.

  Definition trivialProver_correct : ProverT_correct trivialProver fs.
  Proof.
    eapply composite_ProverT_correct; 
      auto using reflexivityProver_correct, assumptionProver_correct.
  Qed.
End typed.