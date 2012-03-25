Require Import DepList List.
Require Import Expr SepExpr SymEval.
Require Import Memory SepIL SymIL SepTac.
Require Import Provers.

Set Implicit Arguments.
Set Strict Implicit.

Module BedrockPtsToEvaluator (P : EvaluatorPluginType BedrockHeap SepIL.ST).
  Module Import SEP := P.SEP.

  Definition pcIndex : nat := 0.
  Definition stateIndex : nat := 1.
  Definition pcT := tvType pcIndex.
  Definition stT := tvType stateIndex.
  
  Definition wordIndex := 0.
  Definition ptrIndex := 0.

  Section parametric.
    Variable types' : list type.
    Definition types := bedrock_types ++ types'.
  
    Definition ptsto32_ssig : ssignature types pcT stT.
    refine (
      {| SepExpr.SDomain := tvType ptrIndex :: tvType wordIndex :: nil
       ; SepExpr.SDenotation := _
       |}).
    refine (ptsto32 _).
    Defined.

    Variable funcs : functions types.

    Variable EqProver : EqProverT funcs.

    Definition expr_equal (summary : eq_summary EqProver) (tv : tvar) (a b : expr types) : bool :=
      match seq_dec a b with
        | Some _ => true
        | None => eq_prove _ summary a b 
      end.
    
    Theorem expr_equal_correct : 
      forall (sum : eq_summary EqProver) (tv : tvar) (a b : expr types),
        expr_equal sum tv a b = true ->
        forall uvars vars,
          eq_valid EqProver uvars vars sum ->
          match exprD funcs uvars vars a tv , exprD funcs uvars vars b tv with 
            | Some l , Some r => l = r
            | _ , _ => True
          end.
    Proof.
      unfold expr_equal. intros. destruct (seq_dec a b); subst.
      destruct (exprD funcs uvars vars0 b tv); auto.
      generalize (eq_prove_correct (uvars := uvars) (vars := vars0) EqProver sum H0). intro.
      case_eq (exprD funcs uvars vars0 a tv); auto.
      case_eq (exprD funcs uvars vars0 b tv); auto. intros.
      unfold ValidExp in *. apply H1 in H; eauto. clear H1.
      destruct H.
      cutrewrite (x = tv) in H.
      rewrite H2 in *. rewrite H3 in *. auto.

      revert H0.
      case_eq (exprD funcs uvars vars0 a x); intros; try contradiction.
      assert (exprD funcs uvars vars0 a x <> None) by congruence.
      assert (exprD funcs uvars vars0 a tv <> None) by congruence.
      eapply exprD_det; eauto.
      rewrite H0 in *. contradiction.
    Qed.      

  Definition sym_read_word_ptsto32 (hyps : eq_summary EqProver) (args : list (expr types)) (p : expr types) 
    : option (expr types) :=
    match args with
      | p' :: v' :: nil => 
        if expr_equal hyps (tvType ptrIndex) p p' then Some v' else None
      | _ => None
    end.
  Definition sym_write_word_ptsto32 (hyps : eq_summary EqProver) (args : list (expr types)) (p v : expr types)
    : option (list (expr types)) :=
    match args with
      | p' :: v' :: nil =>
        if expr_equal hyps (tvType ptrIndex) p p' then Some (p :: v :: nil) else None
      | _ => None
    end.

  Ltac expose :=
    repeat (unfold wordIndex, ptrIndex in *; 
            match goal with 
              | [ H : match applyD _ _ ?A _ _ with
                        | Some _ => _ 
                        | None => False 
                      end |- _ ] =>
              destruct A; simpl in H; try (exfalso; assumption)
              | [ H : context [ match exprD ?A ?B ?C ?D ?E with
                          | None => _
                          | Some _ => _
                        end ] |- _ ] =>
              revert H; case_eq (exprD A B C D E); simpl; intros; 
                try (exfalso; assumption)
              | [ H : context [ match expr_equal ?A ?B ?C ?D with
                                  | true => _
                                  | false => _
                                end ] |- _ ] =>
                revert H; case_eq (expr_equal A B C D); intros; 
                  try (exfalso; congruence)
              | [ H : expr_equal ?A ?B ?C ?D = true 
                , H' : AllProvable _ _ _ ?A |- _ ] =>
                generalize (@expr_equal_correct _ _ _ _ H _ _ H'); clear H; intros
              | [ H : Some _ = Some _ |- _ ] =>
                inversion H; clear H; subst
              | [ H : exprD _ _ _ _ _ = Some _ |- _ ] =>
                rewrite H in *
            end; simpl in * ).

  Lemma sym_read_ptsto32_correct : forall args uvars vars cs hyps pe p ve m stn,
    sym_read_word_ptsto32 hyps args pe = Some ve ->
    eq_valid EqProver uvars vars hyps ->
    exprD funcs uvars vars pe (tvType ptrIndex) = Some p ->
    match 
      applyD (exprD funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match exprD funcs uvars vars ve (tvType wordIndex) with
      | Some v =>
        ST.HT.smem_get_word (IL.implode stn) p m = Some v
      | _ => False
    end.
  Proof.
    simpl; intros.
    unfold sym_read_word_ptsto32 in H.
    repeat (destruct args; try congruence).
    revert H.
    case_eq (expr_equal hyps (tvType ptrIndex) pe e); try congruence.
    intros.
    inversion H3; clear H3; subst.
    eapply expr_equal_correct in H; eauto.
    simpl applyD in H2.
    expose; try congruence.
    unfold ST.satisfies in H6. PropXTac.propxFo. 
  Qed.

  Lemma sym_write_word_ptsto32_correct : forall args uvars vars cs hyps pe p ve v m stn args',
    sym_write_word_ptsto32 hyps args pe ve = Some args' ->
    eq_valid EqProver uvars vars hyps ->
    exprD funcs uvars vars pe (tvType ptrIndex) = Some p ->
    exprD funcs uvars vars ve (tvType wordIndex) = Some v ->
    match
      applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some p => ST.satisfies cs p stn m
    end ->
    match 
      applyD (@exprD _ funcs uvars vars) (SDomain ptsto32_ssig) args' _ (SDenotation ptsto32_ssig)
      with
      | None => False
      | Some pr => 
        match ST.HT.smem_set_word (IL.explode stn) p v m with
          | None => False
          | Some sm' => ST.satisfies cs pr stn sm'
        end
    end.
  Proof.
    simpl; intros; expose.

    unfold ST.satisfies in *. PropXTac.propxFo. 
    case_eq (smem_set_word (IL.explode stn) p v m).
    intros. unfold ptsto32. PropXTac.propxFo.
    eapply smem_set_get_word_eq; eauto.
    eapply IL.implode_explode.
    eapply expr_equal_correct in H; eauto.
    rewrite H1 in H. rewrite H3 in H. subst.
    eapply smem_set_get_valid_word; eauto.
  Qed.  

  Definition SymEval_ptsto32 : @P.SymEval types stT pcT
    (tvType ptrIndex) (tvType wordIndex)
    SepTac.smem_read
    SepTac.smem_write
    funcs (eq_summary EqProver) (eq_valid EqProver) ptsto32_ssig.
  eapply P.Build_SymEval.
  eapply sym_read_ptsto32_correct.
  eapply sym_write_word_ptsto32_correct.
  Defined.  

  End parametric.

End BedrockPtsToEvaluator.

Module DEMO := BedrockPtsToEvaluator SymIL.PLUGIN.

Import BedrockEvaluator.

Record mem_evaluator : Type :=
{ READER : _ 
; WRITER : _
; CORRECTNESS : BedrockEvaluator.Correctness READER WRITER
}.

(** TODO: I need to find some way to build this using tactics! **)
Definition ptsto_evaluator : mem_evaluator.
refine (
  {| READER := fun typs hyps p s =>
    match FM.find 0 (impures s) with
      | None => None
      | Some argss =>
        @fold_args unit (fun _ => unit) (bedrock_types ++ typs) (expr (bedrock_types ++ typs)) 
          (fun _ _ args =>
            match args with
              | p' :: v' :: nil => 
                if DEMO.expr_equal _ hyps (tvType 0) p p' then Some v' else None
              | _ => None
            end)
          tt tt argss
    end
   ; WRITER := fun typs hyps p v s => 
     match FM.find 0 (impures s) with
      | None => None
      | Some argss =>
        let res :=
          @fold_args_update unit (fun _ => unit) (bedrock_types ++ typs)
            (fun _ _ args =>
              match args with
                | p' :: v' :: nil => 
                  if DEMO.expr_equal _ hyps (tvType 0) p p' then Some (p' :: v :: nil) else None
                | _ => None
              end)
            tt tt argss
        in
        match res with
          | None => None
          | Some res =>
            Some {| impures := FM.add 0 res (impures s) ; pures := pures s ; other := other s |}
        end
    end
   ; CORRECTNESS := 
     {| TypeImage := nil
      ; FuncImage := fun _ => nil
      ; PredImage := fun t => (0, DEMO.ptsto32_ssig t) :: nil
      ; ReadCorrect := _
      ; WriteCorrect := _
      |}
   |}); unfold READER, WRITER.
admit.
admit.
Defined.