Require Import List Bool.
Require Import Expr.
Require Import ExprUnify.
Require Import Instantiation.

Module Make (S : Subst) <: SyntacticUnifier S.
  Section typed.
    Variable types : list type.

    Section unify.
      Variable exprUnify : expr -> expr -> S.Subst -> option S.Subst.      

      Fixpoint unify (l r : expr) (sub : S.Subst) : option S.Subst :=
        match l , r with
(*          | Const t v , Const t' v' => 
            match equiv_dec t t' with
              | left pf => match pf in _ = k return tvarD _ k -> _ with
                             | refl_equal => fun v' =>
                               if get_Eq types t v v'
                                 then Some sub
                                 else None
                           end v'
              | right _ => None
            end *)
          | Var v , Var v' => 
            if Peano_dec.eq_nat_dec v v' 
              then Some sub
              else None
          | Func f1 args1 , Func f2 args2 =>
            if EqNat.beq_nat f1 f2 then
              (fix unifyArgs (args1 args2 : list (expr)) (s : S.Subst) 
                : option S.Subst :=
                match args1 , args2 with
                  | nil , nil => Some s
                  | nil , _ :: _ => None
                  | _ :: _ , nil => None
                  | arg1 :: args1 , arg2 :: args2 =>
                    match unify arg1 arg2 s with
                      | None => None
                      | Some s => unifyArgs args1 args2 s
                    end
                end) args1 args2 sub
              else None
          | Equal t1 e1 f1 , Equal t2 e2 f2 =>
            if equiv_dec t1 t2 then
              match unify e1 e2 sub with
                | None => None
                | Some sub => unify f1 f2 sub
              end
              else
                None
          | Not e1 , Not e2 =>
            unify e1 e2 sub
          | UVar l , UVar r => 
            if EqNat.beq_nat l r then Some sub
              else 
                match S.Subst_lookup l sub with
                  | None => S.Subst_set l (UVar r) sub
                  | Some l' =>
                    match S.Subst_lookup r sub with
                      | None => S.Subst_set r l' sub
                      | Some r' =>
                        exprUnify l' r' sub
                    end
                end
          | UVar u , r =>
            match S.Subst_lookup u sub with
              | None =>
                S.Subst_set u r sub
              | Some l' =>
                exprUnify l' r sub
            end
          | l , UVar u =>
            match S.Subst_lookup u sub with
              | None => 
                S.Subst_set u l sub
              | Some r' =>
                exprUnify l r' sub
            end
          | _ , _ => None
        end.
    End unify.

    Fixpoint exprUnify (bound : nat) : expr -> expr -> S.Subst -> option S.Subst :=
      match bound with 
        | 0 => fun _ _ _ => None
        | S bound =>
          fix unify (l r : expr) (sub : S.Subst) : option S.Subst :=
            match l , r with
(*              | Const t v , Const t' v' => 
                match equiv_dec t t' with
                  | left pf => match pf in _ = k return tvarD _ k -> _ with
                                 | refl_equal => fun v' =>
                                   if get_Eq types t v v'
                                     then Some sub
                                     else None
                               end v'
                  | right _ => None
                end *)
              | Var v , Var v' => 
                if EqNat.beq_nat v v' 
                  then Some sub
                  else None
              | Func f1 args1 , Func f2 args2 =>
                if EqNat.beq_nat f1 f2 then
                  (fix unifyArgs (args1 args2 : list (expr)) (s : S.Subst) 
                    : option S.Subst :=
                    match args1 , args2 with
                      | nil , nil => Some s
                      | nil , _ :: _ => None
                      | _ :: _ , nil => None
                      | arg1 :: args1 , arg2 :: args2 =>
                        match unify arg1 arg2 s with
                          | None => None
                          | Some s => unifyArgs args1 args2 s
                        end
                    end) args1 args2 sub
                  else None
              | Equal t1 e1 f1 , Equal t2 e2 f2 =>
                if equiv_dec t1 t2 then
                  match unify e1 e2 sub with
                    | None => None
                    | Some sub => unify f1 f2 sub
                  end
                  else
                    None
              | Not e1 , Not e2 =>
                unify e1 e2 sub
              | UVar l , UVar r => 
                if EqNat.beq_nat l r then Some sub
                  else 
                    match S.Subst_lookup l sub with
                      | None => S.Subst_set l (UVar r) sub
                      | Some l' =>
                        match S.Subst_lookup r sub with
                          | None => S.Subst_set r l' sub
                          | Some r' =>
                            exprUnify bound l' r' sub
                        end
                    end
              | UVar u , r =>
                match S.Subst_lookup u sub with
                  | None =>
                    S.Subst_set u r sub
                  | Some l' =>
                    exprUnify bound l' r sub
                end
              | l , UVar u =>
                match S.Subst_lookup u sub with
                  | None => 
                    S.Subst_set u l sub
                  | Some r' =>
                    exprUnify bound l r' sub
                end
              | _ , _ => None
            end
      end.

    Hint Rewrite S.exprInstantiate_Func S.exprInstantiate_Equal S.exprInstantiate_Not 
      S.exprInstantiate_UVar S.exprInstantiate_Var : subst_simpl.

    Opaque S.Subst_lookup S.Subst_set S.exprInstantiate.

    Require Import ExtLib.Tactics.Consider.

    Theorem unify_uvar : forall (u : uvar) (sub sub' : S.Subst)
      (o : expr -> expr -> S.Subst -> option S.Subst),
      (forall (l r : expr) (sub0 sub'0 : S.Subst),
        o l r sub0 = Some sub'0 ->
        S.exprInstantiate sub'0 l = S.exprInstantiate sub'0 r /\
        S.Subst_Extends sub'0 sub0 /\
        (forall (funcs : tfunctions) (U G : tenv) (t : tvar),
          is_well_typed funcs U G l t = true ->
          is_well_typed funcs U G r t = true ->
          S.Subst_WellTyped funcs U G sub0 -> S.Subst_WellTyped funcs U G sub'0)) ->
      forall e : expr,
        match S.Subst_lookup u sub with
          | Some r' => o e r' sub
          | None => S.Subst_set u e sub
        end = Some sub' ->
        S.exprInstantiate sub' e = S.exprInstantiate sub' (UVar u) /\
        S.Subst_Extends sub' sub /\
        (forall (funcs : tfunctions) (U G : tenv) (t1 : tvar),
          is_well_typed funcs U G e t1 = true ->
          is_well_typed funcs U G (UVar u) t1 = true ->
          S.Subst_WellTyped funcs U G sub -> S.Subst_WellTyped funcs U G sub').
    Proof.
      intros. consider (S.Subst_lookup u sub); intros.
      { specialize (H _ _ _ _ H1). rewrite S.exprInstantiate_UVar.
        intuition.
        { erewrite S.Subst_lookup_Extends by eassumption. auto. }
        { eapply H4; try eassumption.
          destruct (S.WellTyped_lookup H6 H0). intuition. simpl in H5.
          rewrite H8 in *.
          destruct (nth_error U u); try congruence.
          consider (tvar_seqb t1 x); congruence. } }
      { clear H; intuition. 
        { erewrite S.Subst_set_exprInstantiate by eassumption; auto. }
        { eapply S.Subst_set_Extends; eauto. }
        { eapply S.Subst_set_WellTyped; try eassumption. simpl in H2.
          destruct (nth_error U u); try congruence.
          consider (tvar_seqb t1 t); congruence. } }
    Qed.

    Lemma exprUnify_all : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
         (S.exprInstantiate sub' l = S.exprInstantiate sub' r)
      /\ (S.Subst_Extends sub' sub)
      /\ (forall funcs U G t,
            is_well_typed funcs U G l t = true ->
            is_well_typed funcs U G r t = true ->
            S.Subst_WellTyped funcs U G sub ->
            S.Subst_WellTyped funcs U G sub').
    Proof.
      induction n; simpl in *; try congruence.
      induction l; simpl in *.
(*      { destruct r; simpl in *; intros; try congruence.
        { consider (equiv_dec t t1); unfold equiv in *; simpl in *; intros; subst; try congruence.
          consider (get_Eq types t1 t0 t2); try congruence; simpl in *; intros.
          inversion H0; clear H0; subst. split; [ reflexivity | split; [ reflexivity | ] ].
          intros. consider (tvar_seqb t1 t); intros; subst; auto. }
        { eapply unify_uvar; eauto. } } *)
      { destruct r; simpl in *; intros; try congruence.
        { consider (EqNat.beq_nat x v); try congruence; subst; intros.
          inversion H0; clear H0; subst. intuition. }
        { eapply unify_uvar; eauto. } }
      { do 4 intro.
        assert ((exists u, r = UVar u) \/
                match S.Subst_lookup x sub with
                  | Some l' => exprUnify n l' r sub
                  | None => S.Subst_set x r sub
                end = Some sub').
        { destruct r; auto. left. eauto. }
        destruct H0.
        { destruct H0; subst.
          consider (EqNat.beq_nat x x0); intros; subst.
          { inversion H0; clear H0; subst. intuition. }
          { consider (S.Subst_lookup x sub); intros.
            { consider (S.Subst_lookup x0 sub); intros.
              { repeat rewrite S.exprInstantiate_UVar.
                specialize (IHn _ _ _ _ H2). destruct IHn as [ ? [ ? ? ] ].
                repeat erewrite S.Subst_lookup_Extends by eassumption.
                intuition. 
                simpl in *; consider (nth_error U x); consider (nth_error U x0); intros.
                consider (tvar_seqb t t0); consider (tvar_seqb t t1); intros.
                subst. subst.
                destruct (S.WellTyped_lookup H8 H0).
                destruct (S.WellTyped_lookup H8 H1).
                rewrite H6 in *. rewrite H9 in *.
                intuition. inversion H11; inversion H7; subst. subst.
                eapply H5; eauto. } 
              { intuition.
                { erewrite S.Subst_set_exprInstantiate with (x := x0) by eassumption.
                  rewrite S.exprInstantiate_UVar.
                  erewrite S.Subst_lookup_Extends; try eassumption.
                  reflexivity. eapply S.Subst_set_Extends; eauto. }
                { eapply S.Subst_set_Extends; eauto. }
                { simpl in *. 
                  consider (nth_error U x); consider (nth_error U x0); intros.
                  consider (tvar_seqb t t0); consider (tvar_seqb t t1); intros; subst.
                  eapply S.Subst_set_WellTyped; try eassumption.
                  subst.
                  destruct (S.WellTyped_lookup H5 H0); intuition.
                  rewrite H6 in *. inversion H7. subst. auto. } } }
            { intuition.
              { erewrite S.Subst_set_exprInstantiate with (x := x) by eassumption. 
                reflexivity. }
              { eapply S.Subst_set_Extends; eauto. }
              { simpl in *. 
                consider (nth_error U x); consider (nth_error U x0); intros.
                consider (tvar_seqb t t0); consider (tvar_seqb t t1); intros; subst.
                eapply S.Subst_set_WellTyped; try eassumption.
                subst. simpl. rewrite H2. consider (tvar_seqb t0 t0); auto. } } } } 
        { clear H. consider (S.Subst_lookup x sub); intros.
          { specialize (IHn _ _ _ _ H0); intuition.
            { rewrite S.exprInstantiate_UVar. 
              erewrite S.Subst_lookup_Extends; try eassumption. }
            { eapply H4; try eassumption.
              destruct (S.WellTyped_lookup H6 H). 
              destruct (nth_error U x); try congruence.
              intuition. inversion H8; clear H8; subst.
              consider (tvar_seqb t x0); try congruence. } }
          { intuition. 
            { erewrite S.Subst_set_exprInstantiate by eassumption. auto. }
            { eapply S.Subst_set_Extends; eauto. }
            { eapply S.Subst_set_WellTyped; eauto.
              destruct (nth_error U x); try congruence.
              consider (tvar_seqb t t0); try congruence. } } } }
      { destruct r; simpl in *; intros; try congruence.
        { consider (EqNat.beq_nat f f0); try congruence; intros; subst.
          intros. apply and_assoc. 
          split.
          { generalize dependent l0; generalize dependent sub; generalize dependent sub'.
            induction H.
            { destruct l0; try congruence. inversion 1; subst. intuition. }
            { destruct l0; try congruence; intros.
              match goal with
                | [ H : match ?X _ _ _ with _ => _ end = _ |- _ ] =>
                  generalize dependent X; intros
              end.
              consider (o x e sub); try congruence; intros.
              specialize (H _ _ _ H1). specialize (IHForall _ _ _ H2). clear H2.
              intuition.
              { simpl. inversion H; clear H; subst.
                repeat rewrite S.exprInstantiate_Func in *.
                simpl. f_equal. inversion H7; f_equal; auto.
                erewrite <- S.exprInstantiate_Extends with (y := s); eauto. rewrite H2.
                rewrite S.exprInstantiate_Extends; auto. }
              { etransitivity; eauto. } } }
          { intros. destruct (nth_error funcs f0); try congruence.
            destruct t0. simpl in *.
            generalize dependent l0; generalize dependent sub; generalize dependent sub'; 
              generalize dependent TDomain.
            induction H.
            { destruct l0; try congruence. } (*inversion 1; subst. 
              destruct (tvar_seqb t TRange); try congruence. auto. } *)
            { destruct l0; try congruence. intros.
              match goal with
                | [ H : match ?X _ _ _ with _ => _ end = _ |- _ ] =>
                  generalize dependent X; intros
              end.
              consider (o x e sub); intros; try congruence.
              specialize (H _ _ _ H2).
              consider (tvar_seqb t TRange); intros; subst. simpl in *.
              destruct TDomain; try congruence.
              consider (is_well_typed funcs U G x t).
              consider (is_well_typed funcs U G e t).
              intuition. eapply H7. 3: eapply H5. eassumption. eauto. eauto. } } }
        { eapply unify_uvar; eauto. } }
      { destruct r; intros; try congruence.
        { consider (equiv_dec t t0); try congruence; unfold equiv in *; simpl in *; intros; subst.
          match goal with
            | [ H : match ?X _ _ _ with _ => _ end = _ |- _ ] =>
              generalize dependent X; intros
          end.
          consider (o l1 r1 sub); try congruence; intros.
          specialize (IHl1 _ _ _ H). specialize (IHl2 _ _ _ H0).
          intuition.
          { do 2 rewrite S.exprInstantiate_Equal. f_equal; auto. 
            erewrite <- S.exprInstantiate_Extends with (y := s); eauto. rewrite H1.
            rewrite S.exprInstantiate_Extends; auto. }
          { etransitivity; eauto. }
          { destruct t; try congruence.
            eapply andb_true_iff in H4. eapply andb_true_iff in H8. intuition eauto. } }
        { eapply unify_uvar; eauto. } }
      { destruct r; intros; try congruence.
        { specialize (IHl _ _ _ H). clear H. intuition eauto. 
          repeat rewrite S.exprInstantiate_Not. rewrite H. auto.
          destruct t; try congruence. simpl in *. eauto. } 
        { eapply unify_uvar; eauto. } }
    Qed.

    Theorem exprUnify_sound_syn : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.exprInstantiate sub' l = S.exprInstantiate sub' r.
    Proof.
      intros. specialize (exprUnify_all _ _ _ _ _ H); intuition.
    Qed.

    Theorem exprUnify_sound_sem : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
      @exprD types funcs U G (S.exprInstantiate sub' l) t = 
      exprD funcs U G (S.exprInstantiate sub' r) t.
    Proof.
      intros. f_equal. specialize (exprUnify_all _ _ _ _ _ H); intuition. 
    Qed.

    Theorem exprUnify_Extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.Subst_Extends sub' sub.
    Proof.
      intros. specialize (exprUnify_all _ _ _ _ _ H); intuition.
    Qed.

    Theorem exprUnify_WellTyped : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
        is_well_typed funcs U G l t = true ->
        is_well_typed funcs U G r t = true ->
        S.Subst_WellTyped funcs U G sub ->
        S.Subst_WellTyped funcs U G sub'.
    Proof.
      do 6 intro. specialize (exprUnify_all _ _ _ _ _ H); intuition.
    Qed.

  End typed.
End Make.
