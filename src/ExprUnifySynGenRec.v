Require Import Expr.
Require Import NatMap.
Require Import EquivDec.
Require Import List Bool.
Require Folds.
Require Import ExtLib.Tactics.Consider.
Require ExtLib.Data.Nat.
Require ExtLib.Data.Pair.
Require ExtLib.Recur.GenRec.
Require Import Instantiation.
Require Import ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Inductive R_expr : expr -> expr -> Prop :=
| R_EqualL : forall t l r, R_expr l (Equal t l r)
| R_EqualR : forall t l r, R_expr r (Equal t l r)
| R_Not    : forall e, R_expr e (Not e)
| R_Func   : forall f args arg,
  In arg args -> R_expr arg (Func f args).
  
Lemma wf_R_expr' : well_founded R_expr.
Proof.  
  red; induction a; constructor; inversion 1; try assumption.

  subst. clear H0. generalize dependent y. generalize dependent l. clear.
  induction l; intros; simpl. inversion H3.
  inversion H3. inversion H. rewrite H0 in H4; assumption.
  inversion H; apply IHl; auto.
Defined.

Lemma wf_R_expr : well_founded R_expr.
Proof.
  let v := eval cbv beta iota zeta delta [ wf_R_expr' list_ind list_rec list_rect eq_ind eq_ind_r eq_rect eq_sym expr_ind ] in wf_R_expr' in
  exact  v.
Defined.

Module Make (S : Subst) <: SyntacticUnifier S.
  Section typed.
    Variable types : list type.

    (** Unification **) 
    Section fold_in.
      Variable LS : list expr.
      Variable F : forall (l r : expr), S.Subst -> In l LS -> option S.Subst.

      Fixpoint dep_in (ls rs : list expr) (sub : S.Subst) {struct ls} : (forall l, In l ls -> In l LS) -> option S.Subst.
      refine (
        match ls as ls , rs as rs return (forall l, In l ls -> In l LS) -> option S.Subst with
          | nil , nil => fun _ => Some sub
          | l :: ls , r :: rs => fun pf_trans =>
            match F l r sub _ with
              | None => None
              | Some sub => dep_in ls rs sub (fun ls pf => pf_trans _ _)
            end
          | _ , _ => fun _ => None
        end).
        Focus 2.
        refine (or_intror _ pf).
        refine (pf_trans _ (or_introl _ (refl_equal _))).
      Defined.

    End fold_in.

    Definition exprUnify_recursor bound_l 
      (recur : forall a_b, Pair.R_pair Nat.R_nat_S (@R_expr) a_b bound_l -> expr -> S.Subst -> option S.Subst)
      (r : expr) (sub : S.Subst) : option S.Subst.
    refine (
      match bound_l as bound_l
        return (forall a_b, Pair.R_pair Nat.R_nat_S (@R_expr) a_b bound_l -> expr -> S.Subst -> option S.Subst)
        -> option S.Subst
        with
        | (bound,l) =>
          match l as l , r as r 
            return (forall a_b, Pair.R_pair Nat.R_nat_S (@R_expr) a_b (bound, l) -> expr -> S.Subst -> option S.Subst)
            -> option S.Subst
            with
            | Var v , Var v' => fun _ => 
              if Peano_dec.eq_nat_dec v v' 
                then Some sub
                else None
            | Func f1 args1 , Func f2 args2 => fun recur =>
              if EqNat.beq_nat f1 f2 then
                @dep_in args1 (fun l r s pf => recur (bound, l) _ r s) args1 args2 sub (fun _ pf => pf)
              else None
            | Equal t1 e1 f1 , Equal t2 e2 f2 => fun recur =>
              if equiv_dec t1 t2 then
                match recur (bound, e1) _ e2 sub with
                  | None => None
                  | Some sub => recur (bound, f1) _ f2 sub
                end
                else
                  None
            | Not e1 , Not e2 => fun recur =>
              recur (bound,e1) _ e2 sub
            | UVar l , UVar r => 
              if EqNat.beq_nat l r then fun _ => Some sub
              else 
                match S.Subst_lookup l sub with
                  | None => fun _ => S.Subst_set l (UVar r) sub
                  | Some l' =>
                    match S.Subst_lookup r sub with
                      | None => fun _ => S.Subst_set r l' sub
                      | Some r' =>
                        match bound as bound return 
                          (forall a_b, Pair.R_pair Nat.R_nat_S (@R_expr) a_b (bound,UVar l) -> expr -> S.Subst -> option S.Subst)
                          -> option S.Subst with
                          | 0 => fun _ => None
                          | S bound => fun recur => recur (bound, l') _ r' sub
                        end
                    end
                end
            | UVar u , _ =>
              match S.Subst_lookup u sub with
                | None => fun recur =>
                  S.Subst_set u r sub
                | Some l' =>
                  match bound as bound return 
                    (forall a_b, Pair.R_pair Nat.R_nat_S (@R_expr) a_b (bound,UVar u) -> expr -> S.Subst -> option S.Subst)
                    -> option S.Subst with
                    | 0 => fun _ => None
                    | S bound => fun recur => recur (bound, l') _ r sub
                  end
              end
            | l , UVar u =>
              match S.Subst_lookup u sub with
                | None => fun recur =>
                  S.Subst_set u l sub
                | Some r' =>
                  match bound as bound return 
                    (forall a_b, Pair.R_pair Nat.R_nat_S (@R_expr) a_b (bound,l) -> expr -> S.Subst -> option S.Subst)
                    -> option S.Subst with
                    | 0 => fun _ => None
                    | S bound => fun recur => recur (bound, l) _ r' sub
                  end
              end
            | _ , _ => fun _ => None
          end 
      end recur
    ); try solve [ apply Pair.L ; constructor | apply Pair.R ; constructor; assumption ].
    Defined.

    (** index by a bound, since the termination argument is not trivial
     ** it is guaranteed to not make more recursions than the number of
     ** uvars.
     **)
    Definition exprUnify (bound : nat) (l : expr) : expr -> S.Subst -> option S.Subst :=
      (@Fix _ _ (GenRec.guard 4 (Pair.wf_R_pair Nat.wf_R_S (@wf_R_expr)))
        (fun _ => expr -> S.Subst -> option S.Subst) exprUnify_recursor) (bound,l).

    (** Proofs **)
    Section equiv.
      Variable A : Type.
      Variable R : A -> A -> Prop.
      Hypothesis Rwf : well_founded R.
      Variable P : A -> Type.
      
      Variable equ : forall x, P x -> P x -> Prop.
      Hypothesis equ_Equiv : forall x, RelationClasses.Equivalence (@equ x).
      
      Variable F : forall x : A, (forall y : A, R y x -> P y) -> P x.

      Lemma Fix_F_equ : forall (x : A) (r : Acc R x),
        equ (@F x (fun (y : A) (p : R y x) => Fix_F P F (Acc_inv r p)))
        (Fix_F P F r).
      Proof.
        eapply Acc_inv_dep; intros.
        simpl in *. reflexivity.
      Qed.

      Lemma Fix_F_inv_equ : 
        (forall (x : A) (f g : forall y : A, R y x -> P y),
          (forall (y : A) (p : R y x), equ (@f y p) (g y p)) -> equ (@F x f) (@F x g)) ->
        forall (x : A) (r s : Acc R x), equ (Fix_F P F r) (Fix_F P F s).
      Proof.
        intro. intro. induction (Rwf x). intros.
        erewrite <- Fix_F_equ. symmetry. erewrite <- Fix_F_equ. symmetry.
        eapply H. intros. eauto.
      Qed.

    End equiv.

    Lemma Equiv_equiv : Equivalence
      (fun f g : expr -> S.Subst -> option S.Subst =>
        forall (a : expr) (b : S.Subst), f a b = g a b).
    Proof.
      constructor; eauto.
      red. intros. rewrite H; eauto.
    Qed.

    Lemma exprUnify_recursor_inv : forall (bound : nat)
      e1 e2 (sub : S.Subst) (A B : Acc _ (bound,e1))
      (w : well_founded (Pair.R_pair Nat.R_nat_S R_expr)),
      Fix_F (fun _ : nat * expr => expr -> S.Subst -> option S.Subst)
      exprUnify_recursor A e2 sub =
      Fix_F (fun _ : nat * expr => expr -> S.Subst -> option S.Subst)
      exprUnify_recursor B e2 sub.
    Proof.
      intros.
      eapply (@Fix_F_inv_equ (nat * expr) (Pair.R_pair Nat.R_nat_S R_expr)
        w
        (fun _ : nat * expr => expr -> S.Subst -> option S.Subst)
        (fun x f g => forall a b, f a b = g a b)
        (fun _ => Equiv_equiv)
        exprUnify_recursor).
      clear. intros.
      unfold exprUnify_recursor. destruct x. destruct e; destruct a; auto;
      repeat match goal with 
               | _ => reflexivity
               | [ H : _ |- _ ] => rewrite H
               | [ |- context [ match ?X with 
                                  | _ => _
                                end ] ] => destruct X
             end.
      generalize (fun (l1 : expr) (pf : In l1 l) => pf).
      assert (
        forall l' l0 b, forall i : forall l1 : expr, In l1 l' -> In l1 l,
          dep_in l
          (fun (l1 r0 : expr) (s : S.Subst) (pf : In l1 l) =>
            f (n, l1)
            (Pair.R Nat.R_nat_S R_expr n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i =
          dep_in l
          (fun (l1 r0 : expr) (s : S.Subst) (pf : In l1 l) =>
            g (n, l1)
            (Pair.R Nat.R_nat_S R_expr n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i).
      induction l'; simpl in *; intros; auto.
      destruct l1; auto. 
      rewrite H. destruct (g (n, a)); auto.
      eapply H0.
    Qed.

    Theorem exprUnify_unroll : forall bound l r sub,
      exprUnify bound l r sub = 
      match l , r with
        | Var v , Var v' => 
          if Peano_dec.eq_nat_dec v v' 
            then Some sub
            else None
        | Func f1 args1 , Func f2 args2 =>
          if EqNat.beq_nat f1 f2 then
            Folds.fold_left_2_opt (@exprUnify bound) args1 args2 sub
          else None
        | Equal t1 e1 f1 , Equal t2 e2 f2 =>
          if equiv_dec t1 t2 then
            match exprUnify bound e1 e2 sub with
              | None => None
              | Some sub => exprUnify bound f1 f2 sub
            end
            else
              None
        | Not e1, Not e2 =>
          exprUnify bound e1 e2 sub
        | UVar l , UVar r => 
          if EqNat.beq_nat l r then Some sub
            else 
              match S.Subst_lookup l sub with
                | None => S.Subst_set l (UVar r) sub
                | Some l' =>
                  match S.Subst_lookup r sub with
                    | None => S.Subst_set r l' sub
                    | Some r' =>
                      match bound with
                        | 0 => None
                        | S bound => exprUnify bound l' r' sub
                      end
                  end
              end
        | UVar u , _ =>
          match S.Subst_lookup u sub with
            | None => S.Subst_set u r sub
            | Some l' =>
              match bound with
                | 0 => None
                | S bound => exprUnify bound l' r sub
              end
          end
        | l , UVar u =>
          match S.Subst_lookup u sub with
            | None => S.Subst_set u l sub
            | Some r' =>
              match bound with
                | 0 => None
                | S bound => exprUnify bound l r' sub
              end
          end
        | _ , _ => None
      end.
    Proof.
      intros. unfold exprUnify at 1.
      match goal with
        | [ |- context [ GenRec.guard ?X ?Y ] ] =>
          generalize (GenRec.guard X Y)
      end.
      intros. unfold Fix.
      rewrite <- (@Fix_F_equ (nat * expr) (Pair.R_pair Nat.R_nat_S R_expr)
        (fun _ : nat * expr => expr -> S.Subst -> option S.Subst)
        (fun x f g => forall a b, f a b = g a b)
        (fun _ => Equiv_equiv)
        exprUnify_recursor
        (bound,l)
        (w (bound,l))
        r sub).
      destruct l; destruct r; simpl; intros; auto;
        try solve [
          repeat match goal with
                   | [ |- context [ match ?X with 
                                      | _ => _ 
                                    end ] ] => destruct X
                 end; try solve [ auto | 
                   unfold exprUnify, Fix ;
                     eapply exprUnify_recursor_inv; eauto ] ].
      Focus 2.
      destruct (equiv_dec t t0); auto.
      unfold exprUnify, Fix.
      erewrite exprUnify_recursor_inv; eauto.
      instantiate (1 := (GenRec.guard 4 (Pair.wf_R_pair Nat.wf_R_S (wf_R_expr)) (bound, l1))).
      match goal with 
        | [ |- match ?X with 
                 | _ => _ 
               end = _ ] => destruct X
      end; auto.
      erewrite exprUnify_recursor_inv; eauto.

      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X; auto
      end.
      generalize (fun (l1 : expr) (pf : In l1 l) => pf).
      assert (forall l' l0 sub,
        forall i : (forall l1 : expr, In l1 l' -> In l1 l),
          dep_in l
          (fun (l1 r0 : expr) (s : S.Subst) (pf : In l1 l) =>
            @Fix_F _ _ (fun _ : nat * expr => expr -> S.Subst -> option S.Subst)
            exprUnify_recursor (bound, l1) (@Acc_inv (nat * expr)
              (@Pair.R_pair nat expr Nat.R_nat_S (@R_expr))
              (bound, Func f l) (w (bound, Func f l)) 
              (bound, l1)
              (@Pair.R nat expr Nat.R_nat_S (@R_expr) bound l1
                (Func f l) (R_Func f l l1 pf))) r0 s) l' l0 sub i =
          Folds.fold_left_2_opt (exprUnify bound) l' l0 sub).
      induction l'; simpl; intros; destruct l1; auto.
      erewrite exprUnify_recursor_inv; eauto.
      instantiate (1 := (GenRec.guard 4 (Pair.wf_R_pair Nat.wf_R_S (wf_R_expr)) (bound, a))).
      unfold exprUnify, Fix.
      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X; auto
      end.
      eapply H.
    Qed.

    Lemma fold_left_2_opt_exprUnify_Extends' : forall b l l0 sub sub',
      Folds.fold_left_2_opt (exprUnify b) l l0 sub = Some sub' ->
      Forall
      (fun l : expr =>
        forall (r : expr) (sub sub' : S.Subst),
          exprUnify b l r sub = Some sub' -> S.Subst_Extends sub' sub) l ->
      S.Subst_Extends sub' sub.
    Proof.
      intros.
      generalize dependent l0. generalize dependent sub.
      induction H0; destruct l0; simpl in *; try congruence; intros.
        inversion H; reflexivity. 

      revert H1; case_eq (exprUnify b x e sub); try congruence; intros.
      etransitivity; eauto.
    Qed.

    Theorem exprUnify_Extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.Subst_Extends sub' sub.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; destruct r; simpl in *;
        solve [ 
          repeat (congruence || eauto ||
              solve [ eapply S.Subst_set_Extends; eauto |
                      etransitivity; eauto |
                      reflexivity |
                  eapply fold_left_2_opt_exprUnify_Extends'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => consider X; intros
              end) ].
    Qed.

    Lemma fold_left_2_opt_exprUnify_Extends : forall b l l0 sub sub',
      Folds.fold_left_2_opt (exprUnify b) l l0 sub = Some sub' ->
      S.Subst_Extends sub' sub.
    Proof.
      induction l; destruct l0; simpl in *; try congruence; intros.
        inversion H; subst; reflexivity.
      revert H; case_eq (exprUnify b a e sub); try congruence; intros.
      etransitivity; eauto using exprUnify_Extends.
    Qed.

    Lemma fold_left_2_opt_map_sound' : forall (n : nat) (l l0 : list expr) (sub sub' : S.Subst),
      Folds.fold_left_2_opt (exprUnify n) l l0 sub = Some sub' ->
      Forall
      (fun l1 : expr =>
        forall (r : expr) (sub0 sub'0 : S.Subst),
          exprUnify n l1 r sub0 = Some sub'0 ->
          S.exprInstantiate sub'0 l1 = S.exprInstantiate sub'0 r) l ->
      map (S.exprInstantiate sub') l = map (S.exprInstantiate sub') l0.
    Proof.
      intros.
      generalize dependent l0. revert sub; revert sub'. 
      induction H0; simpl in *; intros; destruct l0; simpl in *; try congruence; auto.
      consider (exprUnify n x e sub); intros; try congruence.
      f_equal;
      eauto using S.exprInstantiate_extends, exprUnify_Extends, fold_left_2_opt_exprUnify_Extends.
    Qed.

    Hint Rewrite S.exprInstantiate_Func S.exprInstantiate_Equal S.exprInstantiate_Not 
      S.exprInstantiate_UVar S.exprInstantiate_Var : subst_simpl.

    Theorem exprUnify_sound_syn : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      S.exprInstantiate sub' l = S.exprInstantiate sub' r.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; destruct r; simpl in *;
        try solve [ 
          repeat (congruence || 
                  solve [ eauto |
                          eapply S.exprInstantiate_extends; eauto using exprUnify_Extends |
                          eapply fold_left_2_opt_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ |- _ ] => erewrite S.Subst_set_exprInstantiate by eauto
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite S.Subst_set_Subst_lookup by eauto
                | [ H : forall (r : expr) (sub sub' : S.Subst _), exprUnify _ _ r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ H')
                | [ H : S.Subst_lookup _ _ = _ |- _ ] =>
                  eapply S.Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_Extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  consider (exprUnify A B C D); intros
                | [ H : match S.Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  consider (S.Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => 
                  consider X; intros
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
                | [ |- _ ] =>
                  rewrite S.exprInstantiate_Func || rewrite S.exprInstantiate_Equal ||
                  rewrite S.exprInstantiate_Not || rewrite S.exprInstantiate_UVar ||
                  rewrite S.exprInstantiate_Var 
              end) ].
      { repeat (congruence || 
                  solve [ eauto |
                          eapply S.exprInstantiate_extends; eauto using exprUnify_Extends |
                          eapply fold_left_2_opt_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ |- _ ] => erewrite S.Subst_set_exprInstantiate by eauto
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite S.Subst_set_Subst_lookup by eauto
                | [ H : forall (r : expr) (sub sub' : S.Subst _), exprUnify _ _ r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ H')
                | [ H : S.Subst_lookup _ _ = _ |- _ ] =>
                  eapply S.Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_Extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  consider (exprUnify A B C D); intros
                | [ H : match S.Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  consider (S.Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => 
                  consider X; intros
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
                | [ |- _ ] => 
                  rewrite S.exprInstantiate_Func || rewrite S.exprInstantiate_Equal ||
                  rewrite S.exprInstantiate_Not || rewrite S.exprInstantiate_UVar ||
                  rewrite S.exprInstantiate_Var
              end).
        eapply S.Subst_set_Extends in H2; try eassumption.
        erewrite S.Subst_lookup_Extends; try eassumption.
        reflexivity. }
      { repeat (congruence || 
                  solve [ eauto |
                          eapply S.exprInstantiate_extends; eauto using exprUnify_Extends |
                          eapply fold_left_2_opt_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] => 
                  unfold Equivalence.equiv in H; subst
                | [ |- _ ] => erewrite S.Subst_set_exprInstantiate by eauto
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite S.Subst_set_Subst_lookup by eauto
                | [ H : forall (r : expr) (sub sub' : S.Subst _), exprUnify _ _ r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ H')
                | [ H : S.Subst_lookup _ _ = _ |- _ ] =>
                  eapply S.Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_Extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] => 
                  consider (exprUnify A B C D); intros
                | [ H : match S.Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  consider (S.Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => 
                  consider X; intros
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
                | [ |- _ ] => 
                  rewrite S.exprInstantiate_Func || rewrite S.exprInstantiate_Equal ||
                  rewrite S.exprInstantiate_Not || rewrite S.exprInstantiate_UVar ||
                  rewrite S.exprInstantiate_Var
              end).
        eapply S.Subst_set_Extends in H2; try eassumption.
        erewrite S.Subst_lookup_Extends; try eassumption.
        reflexivity. }
    Qed.

    Theorem exprUnify_sound_sem : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
      exprD (types := types) funcs U G (S.exprInstantiate sub' l) t = 
      exprD funcs U G (S.exprInstantiate sub' r) t.
    Proof.
      intros. apply exprUnify_sound_syn in H. rewrite H. reflexivity.
    Qed.

    Lemma exprUnify_WellTyped_Forall : forall n (l : list expr),
      Forall
      (fun l0 : expr =>
        forall (r : expr) (sub sub' : S.Subst),
          exprUnify n l0 r sub = Some sub' ->
          forall (funcs : tfunctions) (U G : tenv) (t : tvar),
            is_well_typed funcs U G l0 t = true ->
            is_well_typed funcs U G r t = true ->
            S.Subst_WellTyped funcs U G sub -> S.Subst_WellTyped funcs U G sub') l ->
      forall (funcs : tfunctions) (U G : tenv) (sub' : S.Subst) 
        (l0 : list tvar) (sub : S.Subst),
        S.Subst_WellTyped funcs U G sub ->
        forall l1 : list expr,
          Folds.fold_left_2_opt (exprUnify n) l l1 sub = Some sub' ->
          Folds.all2 (is_well_typed funcs U G) l1 l0 = true ->
          Folds.all2 (is_well_typed funcs U G) l l0 = true ->
          S.Subst_WellTyped funcs U G sub'.
    Proof.
      induction 1; simpl; intros.
      { destruct l0; destruct l1; simpl in *; auto; try congruence. }
      { destruct l1; destruct l0; try congruence. simpl in *.
        repeat match goal with
                 | [ H : context [ match ?X with 
                                     | _ => _ 
                                   end ] |- _ ] =>
                 revert H; case_eq X; try congruence; intros
               end. eauto. }
    Qed.    

    Require ExtLib.Structures.EqDep.

    Theorem Subst_lookup_WellTyped_guard : forall funcs U G (sub : S.Subst),
      S.Subst_WellTyped funcs U G sub ->
      forall u e,
        S.Subst_lookup u sub = Some e ->
        forall t,
          nth_error U u = Some t ->
          is_well_typed funcs U G e t = true.
    Proof.
      intros. eapply S.WellTyped_lookup in H0; eauto. destruct H0. rewrite H1 in *; intuition.
      inversion H2; auto.
    Qed.

    Hint Extern 1 (is_well_typed _ _ _ _ _ = _) =>
      simpl;
        repeat match goal with 
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- _ ] => rewrite EquivDec_refl_left
                 | [ |- _ ] => rewrite tvar_seqb_refl
               end; reflexivity : exprs.

    Theorem exprUnify_WellTyped : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
        is_well_typed funcs U G l t = true ->
        is_well_typed funcs U G r t = true ->
        S.Subst_WellTyped funcs U G sub ->
        S.Subst_WellTyped funcs U G sub'.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; unfold get_Eq in *; destruct r; simpl in *;
        try congruence;
        repeat (match goal with
                 | [ H : (if ?X then _ else _) = _ |- _ ] =>
                   (revert H; consider X; intros; try congruence); [ try subst ]
                 | [ H : context [ @equiv_dec ?A ?B ?C ?E ?X ?Y ] |- _ ] =>
                   destruct (@equiv_dec A B C E X Y); unfold equiv in *; subst; try congruence
                 | [ H : context [ match ?T with
                                     | tvProp => _
                                     | tvType _ => _
                                   end ] |- _ ] => (destruct T; try congruence); [ ] 
                 | [ H : context [ match nth_error ?X ?Y with
                                     | _ => _ 
                                   end ] |- _ ] => 
                   consider (nth_error X Y); intros; try congruence
                 | [ H : context [ match S.Subst_lookup ?X ?Y with
                                     | _ => _ 
                                   end ] |- _ ] => 
                   consider (S.Subst_lookup X Y); intros; try congruence
                 | [ H : (if ?X then _ else _) = _ |- _ ] =>
                   first [ solve [ consider X; intros; try congruence ]
                         | (consider X; intros; try congruence); [ ] ]
                 | [ H : ?X = _ , H' : ?X = _ |- _ ] => rewrite H in H'
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ H : context [ match exprUnify ?A ?B ?C ?D with _ => _ end ] |- _ ] => 
                   consider (exprUnify A B C D); intros; try congruence
                 | [ H : _ && _ = true |- _ ] => eapply andb_true_iff in H; destruct H
                 | [ H : forall a b c d, exprUnify ?n a b c = Some d -> _ , H' : exprUnify ?n _ _ _ = Some _ |- _ ] =>
                   (eapply H in H'; (eauto using Subst_lookup_WellTyped_guard, S.Subst_set_WellTyped with exprs)); 
                   instantiate; eauto with exprs
                 | [ H : ?X = ?X , H' : context [ match ?H with _ => _ end ] |- _ ] =>
                   rewrite (EqDep.UIP_refl H) in H'
                 | [ |- _ ] => try unfold equiv in *; progress subst 
               end);
        try solve [ eauto using Subst_lookup_WellTyped_guard, S.Subst_set_WellTyped with exprs
              | (eapply S.Subst_set_WellTyped; eauto); simpl;
                repeat match goal with
                         | [ H : _ = _ |- _ ] => rewrite H
                         | [ |- _ ] => rewrite EquivDec_refl_left
                         | [ |- _ ] => rewrite tvar_seqb_refl
                       end; auto 
          | eauto using exprUnify_WellTyped_Forall].
    Qed.

  End typed.
End Make.
