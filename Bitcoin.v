(* Checked with Coq version 8.10.2 *)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Program.Basics.
Require Import Coq.Sorting.Permutation.

Require Import BC.Utils.

Open Scope list_scope.

Import ListNotations.

(** Currency denomination *)
Definition Satoshi := nat.

(* Use instead of plain nat to clarify signatures *)
Definition Index := nat.
Definition Time := nat.

(** Public key for signature verification *)
Inductive PK := key_pk : nat -> PK.

(** Secret key for signing *)
Inductive SK := key_sk : nat -> SK.

(** The keys are considered to be paired if they wrap the same nat. *)
Definition is_key_pair (pk : PK) (sk : SK) : bool :=
  match pk, sk with
  | key_pk n1, key_sk n2 => beq_nat n1 n2
  end.

(** SIGHASH flags.
    See https://bitcoin.org/en/developer-guide#signature-hash-types for explanations. *)
Inductive Modifier : Type :=
  | m_aa : Modifier (* SIGHASH_ALL *)
  | m_an : Modifier (* SIGHASH_NONE *)
  | m_as : Modifier (* SIGHASH_SINGLE *)
  (* _ | SIGHASH_ANYONECANPAY *)
  | m_sa : Modifier
  | m_sn : Modifier
  | m_ss : Modifier.

Scheme Equality for Modifier.
Scheme Equality for SK.
Scheme Equality for PK.
Scheme Equality for prod.
Scheme Equality for string.
Scheme Equality for list.

(* Define these as mutually inductive due to the cycle StackValue -> TxStub -> Exp -> StackValue *)
Inductive Exp : Set :=
  | e_var : string -> Exp
  | e_const : StackValue -> Exp
  | e_plus : Exp -> Exp -> Exp
  | e_minus : Exp -> Exp -> Exp
  | e_equal : Exp -> Exp -> Exp
  | e_less : Exp -> Exp -> Exp
  | e_if : Exp -> Exp -> Exp -> Exp
  | e_length : Exp -> Exp
  | e_hash : Exp -> Exp
  | e_versig : list PK -> list Exp -> Exp
  | e_abs_after: Time -> Exp -> Exp
  | e_rel_after: Time -> Exp -> Exp
(* Inductive StackValue *)
with StackValue : Set :=
  | sv_int : Z -> StackValue
  | sv_bool : bool -> StackValue
  | sv_hash : StackValue -> StackValue
  | sv_sig : TxStub -> SK -> Modifier -> Index -> StackValue
(* Inductive TxStub *)
with TxStub : Set :=
  | tx_stub (inputs : list (TxStub * Index * Time)%type) (outputs : list (Exp * Satoshi)) (absLock : Time)
  | coinbase (block_height : nat) (outputs : list (Exp * Satoshi)).

Section Induction.

Variables (P_TxStub : TxStub -> Prop)
          (P_Exp : Exp -> Prop)
          (P_StackValue : StackValue -> Prop).

Hypotheses
      (H_TxStub_tx_stub : forall (inputs : list (TxStub * Index * Time)%type)
                                  (outputs : list (Exp * Satoshi))
                                  (absLock : Time)
                                  (IH_in : forall (tx : TxStub)
                                                (i : Index)
                                                (relLock : Time),
                                                In (tx, i, relLock) inputs -> P_TxStub tx)
                                  (IH_out : forall (s : Exp) (v : Satoshi),
                                                In (s, v) outputs -> P_Exp s),
                                        P_TxStub (tx_stub inputs outputs absLock))
      (H_TxStub_coinbase : forall (block_height : nat)
                                  (outputs : list (Exp * Satoshi))
                                  (IH_out : forall (s : Exp) (v : Satoshi),
                                                In (s, v) outputs -> P_Exp s),
                                        P_TxStub (coinbase block_height outputs))


       (H_Exp_e_var : forall s : string, P_Exp (e_var s))
       (H_Exp_e_const : forall s : StackValue, P_StackValue s -> P_Exp (e_const s))
       (H_Exp_e_plus : forall e : Exp, P_Exp e -> forall e0 : Exp, P_Exp e0 -> P_Exp (e_plus e e0))
       (H_Exp_e_minus : forall e : Exp, P_Exp e -> forall e0 : Exp, P_Exp e0 -> P_Exp (e_minus e e0))
       (H_Exp_e_equal : forall e : Exp, P_Exp e -> forall e0 : Exp, P_Exp e0 -> P_Exp (e_equal e e0))
       (H_Exp_e_less : forall e : Exp, P_Exp e -> forall e0 : Exp, P_Exp e0 -> P_Exp (e_less e e0))
       (H_Exp_e_if : forall e : Exp, P_Exp e -> forall e0 : Exp, P_Exp e0 -> forall e1 : Exp, P_Exp e1 -> P_Exp (e_if e e0 e1))
       (H_Exp_e_length : forall e : Exp, P_Exp e -> P_Exp (e_length e))
       (H_Exp_e_hash : forall e : Exp, P_Exp e -> P_Exp (e_hash e))
       (H_Exp_e_versig : forall (l : list PK) (l0 : list Exp)
                                (IH : forall (e : Exp), In e l0 -> P_Exp e), P_Exp (e_versig l l0))
       (H_Exp_e_abs_after : forall (t : Time) (e : Exp), P_Exp e -> P_Exp (e_abs_after t e))
       (H_Exp_e_rel_after : forall (t : Time) (e : Exp), P_Exp e -> P_Exp (e_rel_after t e))

       (H_StackValue_sv_int : forall z : Z, P_StackValue (sv_int z))
       (H_StackValue_sv_bool : forall b : bool, P_StackValue (sv_bool b))
       (H_StackValue_sv_hash : forall s : StackValue, P_StackValue s -> P_StackValue (sv_hash s))
       (H_StackValue_sv_sig : forall (t : TxStub) (s : SK) (m : Modifier) (i : Index), P_TxStub t -> P_StackValue (sv_sig t s m i)).

Lemma TxStub_induction (tx : TxStub) : P_TxStub tx
with Exp_induction (e : Exp) : P_Exp e
with StackValue_induction (sv : StackValue) : P_StackValue sv.
Proof.
  {
    destruct tx. apply H_TxStub_tx_stub.
    {
      generalize dependent inputs.
      fix list_ind 1. intros.
      destruct inputs; destruct H.
      - destruct p as [[tx' i'] relLock']. inversion H. subst tx. exact (TxStub_induction tx').
      - eapply list_ind; eauto.
    }
    {
      generalize dependent outputs.
      fix list_ind 1. intros.
      destruct outputs; destruct H.
      - destruct p as [s' v']. inversion H. subst s. exact (Exp_induction s').
      - eapply list_ind; eauto.
    }
    {
      apply H_TxStub_coinbase.
      generalize dependent outputs.
      fix list_ind 1. intros.
      destruct outputs; destruct H.
      - destruct p as [s' v']. inversion H. subst s. exact (Exp_induction s').
      - eapply list_ind; eauto.
    }
  }
  {
    destruct e.
    - apply H_Exp_e_var.
    - apply H_Exp_e_const. exact (StackValue_induction s).
    - apply H_Exp_e_plus; apply Exp_induction.
    - apply H_Exp_e_minus; apply Exp_induction.
    - apply H_Exp_e_equal; apply Exp_induction.
    - apply H_Exp_e_less; apply Exp_induction.
    - apply H_Exp_e_if; apply Exp_induction.
    - apply H_Exp_e_length; apply Exp_induction.
    - apply H_Exp_e_hash; apply Exp_induction.
    - apply H_Exp_e_versig.
      generalize dependent l0.
      fix list_ind 1. intros.
      destruct l0; destruct H.
      + subst e. exact (Exp_induction e0).
      + eapply list_ind; eauto.
    - apply H_Exp_e_abs_after; apply Exp_induction.
    - apply H_Exp_e_rel_after; apply Exp_induction.
  }
  {
    destruct sv.
    - apply H_StackValue_sv_int.
    - apply H_StackValue_sv_bool.
    - apply H_StackValue_sv_hash; apply StackValue_induction.
    - apply H_StackValue_sv_sig. exact (TxStub_induction t).
  }
Qed.

End Induction.

Inductive Tx : Set := tx {
  stub : TxStub;
  witnesses : list (list StackValue);
}.

(** The free variables of the expression in left to right order. *)
Fixpoint free_vars (e : Exp) : list string :=
  match e with
  | e_var v => [v]
  | e_const _ => []
  | e_plus e1 e2 => nodup string_dec (free_vars e1 ++ free_vars e2)
  | e_minus e1 e2 => nodup string_dec (free_vars e1 ++ free_vars e2)
  | e_equal e1 e2 => nodup string_dec (free_vars e1 ++ free_vars e2)
  | e_less e1 e2 => nodup string_dec (free_vars e1 ++ free_vars e2)
  | e_if e1 e2 e3 => nodup string_dec (free_vars e1 ++ free_vars e2 ++ free_vars e3)
  | e_length e => free_vars e
  | e_hash e => free_vars e
  | e_versig _ es => nodup string_dec (flat_map free_vars es)
  | e_abs_after _ es => free_vars es
  | e_rel_after _ es => free_vars es
  end.

Reserved Notation "a '==' b" (at level 20).

(* Needed because of boolean equality checking for expression hashes. *)
Fixpoint Exp_beq (e1 : Exp) (e2 : Exp) : bool :=
  match e1, e2 with
  | e_var s1, e_var s2                  => string_beq s1 s2
  | e_const z1, e_const z2              => StackValue_beq z1 z2
  | e_plus e11 e12, e_plus e21 e22      => e11 == e21 && e12 == e22
  | e_minus e11 e12, e_minus e21 e22    => e11 == e21 && e12 == e22
  | e_equal e11 e12, e_equal e21 e22    => e11 == e21 && e12 == e22
  | e_less e11 e12, e_less e21 e22      => e11 == e21 && e12 == e22
  | e_if e11 e12 e13, e_if e21 e22 e23  => e11 == e21 && e12 == e22 && e13 == e23
  | e_length e1, e_length e2            => e1 == e2
  | e_hash e1, e_hash e2                => e1 == e2
  | e_versig pk1 es1, e_versig pk2 es2  => list_beq _ PK_beq pk1 pk2 && list_beq _ Exp_beq es1 es2
  | e_abs_after t1 e1, e_abs_after t2 e2 => beq_nat t1 t2 && e1 == e2
  | e_rel_after t1 e1, e_rel_after t2 e2 => beq_nat t1 t2 && e1 == e2
  | _, _ => false
  end
with StackValue_beq s1 s2 :=
  match s1, s2 with
  | sv_int i1, sv_int i2 => Z.eqb i1 i2
  | sv_bool b1, sv_bool b2 => eqb b1 b2
  | sv_hash v1, sv_hash v2 => StackValue_beq v1 v2
  | sv_sig t1 s1 m1 i1, sv_sig t2 s2 m2 i2 =>
    TxStub_beq t1 t2 && SK_beq s1 s2 && Modifier_beq m1 m2 && beq_nat i1 i2
  | _, _ => false
  end
with TxStub_beq (T1 : TxStub) (T2 : TxStub) : bool :=
  match T1, T2 with
  | tx_stub i1 o1 al1 , tx_stub i2 o2 al2
    => list_beq _ (prod_beq _ _ (prod_beq _ _ TxStub_beq beq_nat) beq_nat) i1 i2
    && list_beq _ (prod_beq _ _ Exp_beq beq_nat) o1 o2
    && beq_nat al1 al2
  | coinbase bh1 o1, coinbase bh2 o2 => beq_nat bh1 bh2 && list_beq _ (prod_beq _ _ Exp_beq beq_nat) o1 o2
  | _, _ => false
  end
where "a '==' b" := (Exp_beq a b).

Lemma list_beq_refl: forall A l eq_dec,
  (forall a, In a l -> eq_dec a a = true)
  -> list_beq A eq_dec l l = true.
Proof.
  intros.
  unfold list_beq.
  induction l; auto.
  assert (In a (a :: l)) by intuition.
  rewrite (H _ H0). intuition.
Qed.

Lemma list_beq_true: forall A l1 l2 eq_dec,
  (forall a1 a2, In a1 l1 -> In a2 l2 -> eq_dec a1 a2 = true -> a1 = a2)
  -> list_beq A eq_dec l1 l2 = true -> l1 = l2.
Proof.
  intros.
  unfold list_beq in H0.
  generalize dependent l2. generalize dependent l1.
  induction l1; destruct l2; try congruence; intros.

  rewrite andb_true_iff in H0. destruct H0. apply H in H0; intuition. subst.
  apply f_equal2; auto.

  apply IHl1; auto.
  intros. apply H; intuition.
Qed.

Lemma prod_beq_refl: forall A B p a b eq_dec_A eq_dec_B,
  p = (a, b) ->
  eq_dec_A a a = true ->
  eq_dec_B b b = true ->
  prod_beq A B eq_dec_A eq_dec_B p p = true.
Proof.
  intros. unfold prod_beq. subst p. intuition.
Qed.

Lemma prod_beq_true: forall A B p1 p2 a1 b1 a2 b2 eq_dec_A eq_dec_B,
  p1 = (a1, b1) ->
  p2 = (a2, b2) ->
  (eq_dec_A a1 a2 = true -> a1 = a2) ->
  (eq_dec_B b1 b2 = true -> b1 = b2) ->
  prod_beq A B eq_dec_A eq_dec_B p1 p2 = true -> p1 = p2.
Proof.
  intros.
  unfold prod_beq in H3.
  subst p1 p2. rewrite andb_true_iff in H3. apply f_equal2; intuition.
Qed.

Lemma string_beq_refl: forall s, string_beq s s = true.
Proof.
  intros.
  induction s; simpl; auto.
  apply andb_true_iff; split; auto.
  destruct a. simpl. repeat rewrite andb_true_iff.
  repeat split; match goal with
  | [ |- bool_beq ?x ?x = true ] => destruct x; auto
  end.
Qed.

Lemma string_beq_true: forall s1 s2, string_beq s1 s2 = true -> s1 = s2.
Proof.
  intros.
  generalize dependent s2.
  induction s1; intros; destruct s2; inversion H; auto.
  rewrite andb_true_iff in H1. destruct H1.
  rewrite (IHs1 _ H1). clear H1 H IHs1.
  apply f_equal2; auto.
  destruct a, a0. simpl in H0. repeat rewrite andb_true_iff in H0. decompose [and] H0.
  repeat match goal with
  | [ H : bool_beq ?x ?y = true |- _ ] => destruct x, y; inversion H; clear H
  end; auto.
Qed.

Lemma beq_nat_nat_beq: forall n1 n2, beq_nat n1 n2 = nat_beq n1 n2.
Proof.
  reflexivity.
Qed.

Lemma TxStub_eq_beq: forall txs, TxStub_beq txs txs = true.
Proof.
  {
    intros.
    induction txs using TxStub_induction with
    (P_TxStub := fun txs => TxStub_beq txs txs = true)
    (P_Exp := fun e => Exp_beq e e = true)
    (P_StackValue := fun sv => StackValue_beq sv sv = true); auto; simpl;
    repeat (apply andb_true_iff; split); auto.
    {
      (* list_beq works correctly on inputs - apply IH *)
      apply list_beq_refl. destruct a as [[tx' i] relLock].
      intros.
      apply prod_beq_refl with (a := (tx', i)) (b := relLock); auto.
      - apply prod_beq_refl with (a := tx') (b := i); auto.
        eapply IH_in; eauto.
        symmetry. apply beq_nat_refl.
      - symmetry. apply beq_nat_refl.
    }
    {
      (* list_beq works correctly on outputs - apply IH_out *)
      apply list_beq_refl. destruct a as [s v]. intros.
      apply prod_beq_refl with (a := s) (b := v).
      reflexivity.

      eapply IH_out; eauto.
      symmetry. apply beq_nat_refl.
    }
    (* absLock and other constructors, trivial reflexivity *)
    all : try (symmetry; apply beq_nat_refl).
    {
      (* list_beq works correctly on outputs - apply IH_out *)
      apply list_beq_refl. destruct a as [s v]. intros.
      apply prod_beq_refl with (a := s) (b := v).
      reflexivity.

      eapply IH_out; eauto.
      symmetry. apply beq_nat_refl.
    }
    apply string_beq_refl.
    all : try apply list_beq_refl; auto.
    - destruct a. simpl. rewrite <- beq_nat_nat_beq. symmetry. apply beq_nat_refl.
    - apply Z.eqb_refl.
    - destruct b; auto.
    - destruct s. simpl. rewrite <- beq_nat_nat_beq. symmetry. apply beq_nat_refl.
    - destruct m; auto.
  }
Qed.

Definition inputs t := match t with tx_stub i _ _ => i | coinbase _ _ => [] end.
Definition outputs t := match t with tx_stub _ o _ => o | coinbase _ o => o end.
Definition absLock t := match t with tx_stub _ _ al => al | _ => 0 end.

Lemma Exp_beq_eq : forall (e1 e2 : Exp), Exp_beq e1 e2 = true -> e1 = e2.
Proof.
  intro e1.
  induction e1 using Exp_induction with
  (P_TxStub := fun tx1 => forall tx2, TxStub_beq tx1 tx2 = true -> tx1 = tx2)
  (P_StackValue := fun sv1 => forall sv2, StackValue_beq sv1 sv2 = true -> sv1 = sv2).
  {
    intros. destruct tx2; simpl in H; try discriminate.
    {
      repeat (rewrite andb_true_iff in H).
      decompose [and] H. clear H.

      apply beq_nat_true in H1. subst absLock0.

      apply list_beq_true in H3. subst outputs0.
      2 : {
        intros. destruct a1, a2.
        eapply prod_beq_true in H1; auto.
        eapply IH_out; eauto.
        apply beq_nat_true.
      }

      apply list_beq_true in H2. subst inputs0. reflexivity.
      {
        clear H2.
        intros.
        case_eq a1; intros. case_eq a2; intros.
        apply (prod_beq_true _ _ a1 a2 p n p0 n0) in H1; subst a1 a2; auto.
        clear H1.
        2 : { apply beq_nat_true. }
        intros.
        case_eq p; intros. case_eq p0; intros.
        apply (prod_beq_true _ _ p p0 t n1 t0 n2) in H1; subst p p0; auto.
        clear H1.
        2 : { apply beq_nat_true. }
        intros.
        exact (IH_in t n1 n H t0 H1).
      }
    }
  }
  {
    intros. destruct tx2; simpl in H; try discriminate.
    {
      repeat (rewrite andb_true_iff in H).
      decompose [and] H. clear H.

      apply list_beq_true in H1. subst outputs0.
      2 : {
        intros. destruct a1, a2.
        eapply prod_beq_true in H3; auto.
        eapply IH_out; eauto.
        apply beq_nat_true.
      }

      apply beq_nat_true in H0. subst block_height0.
      reflexivity.
    }
  }

  all : intros; first [destruct e2 | destruct sv2];
  inversion H; clear H; rename H1 into H_beq;
  repeat (rewrite andb_true_iff in H_beq); decompose [and] H_beq.
  all : try rewrite <- beq_nat_nat_beq in *.
  all : repeat match goal with
  | [ H: ?e1 == ?e2 = true |- context[?e1] ] =>
    match goal with
    | [ IH: forall e, e1 == e = true -> _ |- _ ] => apply IH in H; subst
    end
  end; try reflexivity.
  all : repeat match goal with
  | [ H: (?n1 =? ?n2)%nat = true |- context[?n1] ] => try rewrite <- beq_nat_nat_beq in *; apply beq_nat_true in H; subst
  end; try reflexivity.

  apply string_beq_true in H_beq; subst; auto.
  apply IHe1 in H_beq; subst; auto.

  apply list_beq_true in H0; apply list_beq_true in H; subst; auto; [
  intros; destruct a1, a2; simpl in *; try rewrite <- beq_nat_nat_beq in *; apply beq_nat_true in H2; subst; auto |
  intros; destruct a1, a2; simpl in *; try rewrite <- beq_nat_nat_beq in *; apply beq_nat_true in H3; subst; auto ].

  apply Z.eqb_eq in H_beq; subst; auto.

  destruct b, b0; simpl in H_beq; inversion H_beq; auto.

  apply IHe1 in H_beq; subst; reflexivity.

  apply IHe1 in H; subst.
  destruct s, s0. simpl in H3. rewrite <- beq_nat_nat_beq in *. apply beq_nat_true in H3.
  destruct m, m0; simpl in H2; inversion H2; subst; auto.
Qed.

Lemma TxStub_beq_eq: forall (tx1 tx2 : TxStub), TxStub_beq tx1 tx2 = true -> tx1 = tx2.
Proof.
  intros.
  generalize dependent tx2.
  induction tx1 using TxStub_induction with
  (P_Exp := fun e1 => forall e2, Exp_beq e1 e2 = true -> e1 = e2)
  (P_StackValue := fun sv1 => forall sv2, StackValue_beq sv1 sv2 = true -> sv1 = sv2).
  {
    intros. destruct tx2; simpl in H; try discriminate.
    {
      repeat (rewrite andb_true_iff in H).
      decompose [and] H. clear H.

      apply beq_nat_true in H1. subst absLock0.

      apply list_beq_true in H3. subst outputs0.
      2 : {
        intros. destruct a1, a2.
        eapply prod_beq_true in H1; auto.
        eapply IH_out; eauto.
        apply beq_nat_true.
      }

      apply list_beq_true in H2. subst inputs0. reflexivity.
      {
        clear H2.
        intros.
        case_eq a1; intros. case_eq a2; intros.
        apply (prod_beq_true _ _ a1 a2 p n p0 n0) in H1; subst a1 a2; auto.
        clear H1.
        2 : { apply beq_nat_true. }
        intros.
        case_eq p; intros. case_eq p0; intros.
        apply (prod_beq_true _ _ p p0 t n1 t0 n2) in H1; subst p p0; auto.
        clear H1.
        2 : { apply beq_nat_true. }
        intros.
        exact (IH_in t n1 n H t0 H1).
      }
    }
  }

  {
    intros. destruct tx2; simpl in H; try discriminate.
    {
      repeat (rewrite andb_true_iff in H).
      decompose [and] H. clear H.

      apply list_beq_true in H1. subst outputs0.
      2 : {
        intros. destruct a1, a2.
        eapply prod_beq_true in H3; auto.
        eapply IH_out; eauto.
        apply beq_nat_true.
      }

      apply beq_nat_true in H0. subst block_height0.
      reflexivity.
    }
  }

  all : intros; first [destruct e2 | destruct sv2];
  inversion H; rename H1 into H_beq;
  repeat (rewrite andb_true_iff in H_beq); decompose [and] H_beq.
  all : try rewrite <- beq_nat_nat_beq in *.
  all : try (apply IHtx1 in H0; apply IHtx0 in H1; subst; auto).
  all : try (apply IHtx1 in H_beq; subst; auto).

  apply string_beq_true in H_beq. subst. auto.

  apply IHtx1 in H2. apply IHtx0 in H3. apply IHtx2 in H1. subst. auto.

  apply list_beq_true in H0. apply list_beq_true in H1. subst. auto.
  auto.
  destruct a1, a2. simpl. rewrite <- beq_nat_nat_beq. intros. apply beq_nat_true in H4. subst. auto.

  all : try (apply beq_nat_true in H0; apply IHtx1 in H1; subst; auto).

  apply Z.eqb_eq in H_beq. subst. auto.

  destruct b, b0; simpl in H_beq; inversion H_beq; auto.

  apply beq_nat_true in H1. apply IHtx1 in H0.
  destruct s, s0. simpl in H4. rewrite <- beq_nat_nat_beq in *. apply beq_nat_true in H4.
  destruct m, m0; simpl in H3; inversion H3; subst; auto.
Qed.

Definition e_true := e_equal (e_const (sv_int 1%Z)) (e_const (sv_int 1%Z)).
Definition e_false := e_equal (e_const (sv_int 0%Z)) (e_const (sv_int 1%Z)).
Definition e_and := fun a b => e_if a b e_false.

Notation x := "x".
Notation y := "y".

Definition subst_TxStub_inputs t v :=
  match t with
  | tx_stub i o al => tx_stub v o al
  | other => other
  end.

Definition subst_TxStub_outputs t v :=
  match t with
  | tx_stub i o al => tx_stub i v al
  | coinbase bh o => coinbase bh v
  end.


Notation "t '.[' 'inputs' ':=' value ']'" := (subst_TxStub_inputs t value) (at level 40).
Notation "t '.[' 'outputs' ':=' value ']'" := (subst_TxStub_outputs t value) (at level 40).


(* Used to zero-out fields of TxStub for transaction hashing purposes. *)
Definition null_output := (e_false, 0%nat).

(** Perform the modification on a TxStub that would be performed prior to hashing
    with a given SIGHASH flag. The index may refer to inputs or outputs depending
    on the modifier. *)
Definition modify (m : Modifier) (i : Index) (T : TxStub) : TxStub :=
  match m with
  | m_aa => T
  | m_an => T.[ outputs := [] ]
  | m_as => T.[ outputs := (default_up_to_nth null_output (outputs T) i) ]
  | m_sa => T.[ inputs := (keep_nth (inputs T) i) ]
  | m_sn => T.[ outputs := [] ].[ inputs := (keep_nth (inputs T) i) ]
  | m_ss => T.[ outputs := (default_up_to_nth null_output (outputs T) i) ]
             .[ inputs := (keep_nth (inputs T) i) ]
  end.

(** Transaction hash. It hashes only the "transaction stub", i.e. the transaction
    with witnesses removed as per SegWit. *)
Inductive TxStubHash : Set := tx_hash : TxStub -> Modifier -> Index -> TxStubHash.

(** The purpose of hashes is to be compared,
    so we implement that comparison as a boolean equality function with the required
    semantics; we modify the transactions with their prescribed modifiers and then
    compare field by field for lack of a real hash function. *)
Definition TxStubHash_beq (h1 h2 : TxStubHash) :=
  match h1, h2 with
  | tx_hash t1 m1 i1, tx_hash t2 m2 i2 => TxStub_beq (modify m1 i1 t1) (modify m2 i2 t2)
  end.

(** Transaction signature, i.e. secret key signed transaction hash. *)
Inductive Sig : Set := sig : SK -> Modifier -> Index -> TxStub -> Sig.

(* Needed because of boolean equality checking for expression hashes. *)
Definition Sig_beq (s1 s2 : Sig) : bool :=
  match s1, s2 with
  | sig (key_sk sk1) m1 i1 T1, sig (key_sk sk2) m2 i2 T2 =>
    beq_nat sk1 sk2 && Modifier_beq m1 m2 && beq_nat i2 i2
    (* pretend as if the hash itself was contained in the signature, as it should be *)
    && TxStubHash_beq (tx_hash T1 m1 i1) (tx_hash T2 m2 i2)
  end.

(** Signature with the corresponding SIGHASH flags, in reality encoded as a single
    integer obtained by concatenation. *)
Definition Sigma := (Sig * Modifier)%type.

(** Signature verification function. Returns true if signature was signed by the secret
    key paired with the given public key and if the hashes are equal
    and were obtained using the same SIGHASH flags. *)
Definition ver (pk : PK) (sigma : Sigma) (T : TxStub) (i: Index) : bool :=
  match sigma with
  | (sig sk m' i' T', m) =>
    is_key_pair pk sk
    && Modifier_beq m' m
    && TxStubHash_beq (tx_hash T m i) (tx_hash T' m' i')
  end.

(** Multiple-key-multiple-signature verification. Iteratively attempt to verify the current
    first signature with the current first public key, skipping keys until success.
    Return true if the signatures are exhausted not after the keys. *)
Fixpoint multi_ver (ks : list PK) (sigmas : list Sigma) (T : TxStub) (i : Index) : bool :=
  match sigmas, ks with
  | [], _ => true
  | _, [] => false
  | sigma :: sigmas', pk :: ks' =>
    if ver pk sigma T i
    then multi_ver ks' sigmas' T i
    else multi_ver ks' sigmas T i
  end.

(** Assuming we know which signatures can be verified with which public keys, demonstrate
    the correctnes of multi-signature verification. *)
Goal
  forall ks (k_a k_b k_c : PK) (sigma_p sigma_q : Sigma) (T : TxStub) (i : Index),
  ks = [k_a; k_b; k_c]
  /\ ver k_a sigma_p T i = true /\ ver k_b sigma_q T i = true
  /\ ver k_a sigma_q T i = false /\ ver k_b sigma_p T i = false
  /\ (forall s, ver k_c s T i = false)
  -> multi_ver ks [sigma_p; sigma_q] T i = true
  /\ multi_ver ks [sigma_q; sigma_p] T i = false.
Proof.
  intros; destruct H as (H0 & H1 & H2 & H3 & H4 & H5); subst; split.
  + simpl; rewrite H1; rewrite H2; auto.
  + simpl; rewrite H3; rewrite H2; erewrite H5; auto.
Qed.

(** We use denotational semantics for the expressions. This type represents the possible
    types of values an expression can denote. Bottom denotes an aborted or otherwise
    failed computation, as opposed to simply unsuccessful verification of the script. *)
Inductive Den : Set :=
  | den_z : Z -> Den
  | den_bool : bool -> Den
  | den_sigma : Sigma -> Den
  | den_hash : Den -> Den
  | den_bottom : Den.

(* Again needed for hash equality purposes. Bottom != Bottom *)
Fixpoint Den_beq (d1 d2 : Den) : bool :=
  match d1, d2 with
  | den_z z1, den_z z2 => Z.eqb z1 z2
  | den_bool b1, den_bool b2 => bool_eq b1 b2
  | den_sigma sig1, den_sigma sig2 => prod_beq _ _ Sig_beq Modifier_beq sig1 sig2
  | den_hash d1', den_hash d2' => Den_beq d1' d2'
  | _, _ => false
  end.

(** Return bottom on wrong denotation type. *)
Definition den_z_op (f : Z -> Z -> Den) (d1 d2 : Den) : Den :=
  match d1, d2 with
  | den_z z1, den_z z2 => f z1 z2
  | _, _ => den_bottom
  end.

Definition den_plus := den_z_op (fun z1 z2 => den_z (Z.add z1 z2)).
Definition den_minus := den_z_op (fun z1 z2 => den_z (Z.sub z1 z2)).
Definition den_less := den_z_op (fun z1 z2 => den_bool (Z.ltb z1 z2)).
Definition den_eq (d1 d2 : Den) : Den :=
  match d1, d2 with
  | den_bottom, _ => den_bottom
  | _, den_bottom => den_bottom
  | _, _ => den_bool (Den_beq d1 d2)
  end.

(** Non-short-circuiting if-then-else. *)
Definition den_if (d1 d2 d3 : Den) : Den :=
  match d1, d2, d3 with
  | _, den_bottom, _ => den_bottom
  | _, _, den_bottom => den_bottom
  | den_bool b, d1, d2 => if b then d1 else d2
  | _, _, _ => den_bottom
  end.

(* Required just for the ceiling divison function. *)
Require Import Coq.micromega.ZMicromega.

Definition den_size (d : Den) : Den :=
  match d with
  | den_z z =>
    match z with
    | 0 => den_z 0
    (* ceil( log2(abs(z)) / 7 ) *)
    | z => den_z (ZMicromega.ceiling (Z.log2 (Z.abs z)) 7)
    end
  | _ => den_bottom
  end.

(** Rewrap stack value into denotation. *)
Fixpoint den_sv (s : StackValue) : Den :=
match s with
| sv_int i => den_z i
| sv_bool b => den_bool b
| sv_hash sv => den_hash (den_sv sv)
| sv_sig t SK m i => den_sigma (sig SK m i t, m)
end.

Open Scope nat_scope.
Definition den_time (t1 t2 : Time) (d : Den) := if t1 <=? t2 then d else den_bottom.
Notation "t '.relLock' ( i )" := (option_map snd (nth_error (inputs t) i)) (at level 40).

(** Partial map from variable name to its denotation supplied from the witness
    of the redeeming transaction. *)
Definition Context := list (string * StackValue).
Definition lookup (var : string) (context : Context) : Den :=
  match (find (fun v_d => string_beq (fst v_d) var) context) with
  | Some v_d => den_sv (snd v_d)
  | None => den_bottom
  end.

(** Compute the denotation of the given expression with the parameters:
    the redeeming transaction (without witnesses), the input index,
    and the context built up from the witness and the expressions free variables. *)
Fixpoint denote (T : TxStub) (i : Index) (context : Context) (exp : Exp) : Den :=
  let denote := denote T i context in
  match exp with
  | e_var var => lookup var context
  | e_const val => den_sv val
  | e_plus e1 e2 => den_plus (denote e1) (denote e2)
  | e_minus e1 e2 => den_minus (denote e1) (denote e2)
  | e_equal e1 e2 => den_eq (denote e1) (denote e2)
  | e_less e1 e2 => den_less (denote e1) (denote e2)
  | e_if e1 e2 e3 => den_if (denote e1) (denote e2) (denote e3)
  | e_length e => den_size (denote e)
  | e_hash e =>
    match denote e with
    | den_bottom => den_bottom
    | d => den_hash d
    end
  | e_versig pks es =>
    let to_sigma := (fun d => match d with
                      | den_sigma s => Some s
                      | _ => None end) in
    (* only compute if the list consists entirely of signatures *)
    let sigmas := coerce_list to_sigma (map denote es) in
    match sigmas with
    | Some sigmas => den_bool (multi_ver pks sigmas T i)
    | None => den_bottom
    end
  | e_abs_after t e => den_time t (absLock T) (denote e)
  | e_rel_after t e =>
    match T.relLock(i) with
    | Some rl => den_time t rl (denote e)
    | None => den_bottom
    end
  end.

Notation "t '.wit' ( i )" := (match (nth_error (witnesses t) i) with Some wit => wit | _ => [] end) (at level 40).
Notation "t '.in' ( i )" := (nth_error (inputs (stub t)) i) (at level 40).
Notation "t '.out' ( i )" := (nth_error (outputs (stub t)) i) (at level 40).

Definition make_context (e : Exp) (w : list StackValue) := (combine (free_vars e) w).

(** We say that the i-th input of T verifies e if its witness provides the correct number of arguments to the script
    and they evaluate the script to true. *)
(* The verification function also requires that all the arguments are given to the expression. *)
Inductive verifies (T : Tx) (i : Index) (e : Exp) : Prop :=
  | mkverifies :
    length (free_vars e) = length (T.wit(i))
    -> denote (stub T) i (make_context e (T.wit(i))) e = den_bool true
    -> verifies T i e.

Definition den_is_true d :=
  match d with
  | den_bool t => t
  | _ => false
  end.

(* We need a decision process for verification later. *)
Definition verifies_dec (T : Tx) (i : Index) (e : Exp) : bool :=
  if beq_nat (length (free_vars e)) (length (T.wit(i)))
  then den_is_true (denote (stub T) i (make_context e (T.wit(i))) e)
  else false.

(** Verification examples *)

Section VerificationExamples.

(* We want an example of the verification function in action. First we create some test values. *)
Let idx := 17%nat.
Let test_SK := key_sk idx.
Let test_PK := key_pk idx.

Let test_Expr := e_equal (e_hash (e_const (sv_int 4))) (e_hash (e_var y)).
Let test_Tx := tx_stub [] [(test_Expr, 13%nat)] 0.

(* Now we have the initial transaction. We need a transaction which attempts to recover the value in test_Tx. *)
Let redeem_idx := 0%nat.
Let redeem_vals := [sv_int 4].

(* Finally, define the money sink transaction. *)
Let redeem_TxStub := tx_stub [(test_Tx, redeem_idx, 0)] [] 0.
Let redeem_Tx := tx redeem_TxStub [redeem_vals].

Goal verifies redeem_Tx 0%nat test_Expr.
Proof. constructor; reflexivity. Qed.

(* Another expression to verify *)
Let test_Expr_2 :=
  e_and (e_equal (e_hash (e_const (sv_int 4))) (e_hash (e_var x))) (e_versig [test_PK] [e_var y]).

Goal ~ verifies redeem_Tx 0%nat test_Expr_2.
Proof. intros H. inversion H as [Hargs Hscript]. inversion Hargs. Qed.

Let redeem_TxStub_2 := tx_stub [(test_Tx, redeem_idx, 0)] [] 0.
(* The variable x has to be mapped into something that verifies the signature. *)
Let redeem_vals_2 := [sv_int 4; sv_sig redeem_TxStub_2 test_SK m_ss 0%nat].
Let redeem_tx_2 := tx redeem_TxStub_2 [redeem_vals_2].

Goal verifies redeem_tx_2 0%nat test_Expr_2.
Proof. constructor; reflexivity. Qed.

Let redeem_vals_2_fake := [sv_int 4; sv_sig test_Tx test_SK m_ss 0%nat].
Let redeem_Tx_2_fake := tx redeem_TxStub_2 [redeem_vals_2_fake].

Goal ~ verifies redeem_Tx_2_fake 0%nat test_Expr_2.
Proof. intros H. inversion H as [Hargs Hscript]. inversion Hscript. Qed.

Goal ~ verifies (tx redeem_TxStub_2 []) 0%nat test_Expr_2.
Proof. intros H. inversion H as [Hargs _]. inversion Hargs. Qed.

End VerificationExamples.


(** Transaction semantics *)

Definition stub_output := (fun (tx_o_i : Tx * Index) => (stub (fst tx_o_i), snd tx_o_i)).

(* Again, we need a decision routine for these predicates. *)
Definition redeems_output_dec (tx : TxStub) (i : Index) (t : Time) (v : Satoshi)
  (tx' : Tx) (j : Index) (t' : Time) :=
  match tx'.in(j) with
  | Some (stx, i', relLock) =>
    (TxStub_beq stx tx) && (beq_nat i' i)
    && (absLock (stub tx') <=? t')
    && (t + relLock <=? t')
    && match nth_error (outputs tx) i with
      | Some (script, v') =>
        if (v <=? v') (* allow a lesser spent value *)
        then verifies_dec tx' j script
        else false
      | _ => false
      end
  | _ => false
  end.

(** Redeeming examples *)

Section RedeemingExamples.

Let test_Expr := e_equal (e_hash (e_const (sv_int 4))) (e_hash (e_var y)).
Let test_Expr' := e_equal (e_hash (e_const (sv_int 42))) (e_hash (e_var y)).
Let test_Tx := tx_stub [] [(test_Expr, 3%nat); (test_Expr, 3%nat)] 0.
Let test_Tx' := tx_stub [] [(test_Expr, 3%nat); (test_Expr', 3%nat)] 0.

Let redeem_vals := [sv_int 4].

Let redeem_TxStub := tx_stub [(test_Tx, 1, 1)] [] 2.
Let redeem_Tx := tx redeem_TxStub [redeem_vals].
Let redeem_TxStub' := tx_stub [(test_Tx', 1, 1)] [] 2.
Let redeem_Tx' := tx redeem_TxStub' [redeem_vals].

Goal redeems_output_dec test_Tx 1 0 3 redeem_Tx 0 2 = true.
Proof. reflexivity. Qed.

(* Too large sum wanted *)
Goal redeems_output_dec test_Tx 1 0 4 redeem_Tx 0 2 = false.
Proof. reflexivity. Qed.

(* Times out of order *)
Goal redeems_output_dec test_Tx 1 10 3 redeem_Tx 0 2 = false.
Proof. reflexivity. Qed.

(* Relative lock doesn't hold *)
Goal redeems_output_dec test_Tx 1 2 3 redeem_Tx 0 2 = false.
Proof. reflexivity. Qed.

(* Absolute lock doesn't hold *)
Goal redeems_output_dec test_Tx 1 0 3 redeem_Tx 0 1 = false.
Proof. reflexivity. Qed.

(* Wrong output referenced *)
Goal redeems_output_dec test_Tx 0 0 3 redeem_Tx 0 2 = false.
Proof. reflexivity. Qed.

(* Wrong transaction referenced *)
Goal redeems_output_dec test_Tx' 1 0 3 redeem_Tx 0 2 = false.
Proof. reflexivity. Qed.

(* Script verification fails *)
Goal redeems_output_dec test_Tx' 1 0 3 redeem_Tx' 0 2 = false.
Proof. reflexivity. Qed.

End RedeemingExamples.

(** Transaction history *)
Definition TxHistory : Set := list (Tx * Time).

Definition match_tx_hist_stub (tx_hist : TxHistory) (tx : TxStub) : list Tx :=
  fst (split (filter (fun (t:Tx*Time) => TxStub_beq tx (stub (fst t))) tx_hist)).

Definition find_tx_hist (tx_hist : TxHistory) (tx : TxStub) : option (TxStub * Time) :=
  option_map stub_output (find (fun a => TxStub_beq tx (stub (fst a))) tx_hist).

Definition time_tx_hist (tx_hist : TxHistory) tx : option Time := option_map snd (find_tx_hist tx_hist tx).

(* Utility function, checks if any input of tx' redeems j-th output of tx *)
Definition redeems_any (tx : TxStub) j t tx' t' :=
  match nth_error (outputs tx) j with
  | Some (_, v) =>
    existsb (fun (input : Index * (TxStub * Index * Time)) => redeems_output_dec tx j t v tx' (fst input) t') (enumerate_list (inputs (stub tx')))
  (* if there's no such output, it can't be redeemed *)
  | _ => false
  end.

(* Check that some subsequent transaction successfully redeems the j-th output of tx *)
Definition spent_output_dec (tx_hist : TxHistory) (tx : TxStub) j :=
  existsb (fun tx_time' =>
    let t := snd tx_time' in
    let tx' := fst tx_time' in
    TxStub_beq (stub tx') tx && existsb (fun el => (redeems_any tx j t (fst el) (snd el))) (tx_hist))
  (tx_hist).

Lemma spent_output_monotonic: forall tx_hist1 tx_hist2 suff
  (TXH_APPEND: tx_hist2 = tx_hist1 ++ suff) tx j,
  spent_output_dec tx_hist1 tx j = true -> spent_output_dec tx_hist2 tx j = true.
Proof.
  intros. unfold spent_output_dec in *.
  unfold find_tx_hist in *. rewrite TXH_APPEND.
  remember (fun a : Tx * Time => TxStub_beq tx0 (stub (fst a))) as pred.

  apply existsb_exists in H. repeat destruct H.
  apply existsb_exists. exists x.
  assert (In x (tx_hist1 ++ suff)) by intuition.
  split.
  auto.
  rewrite existsb_app.
  rewrite andb_true_iff;
  rewrite andb_true_iff in H0; destruct H0; split; auto.
  apply orb_true_iff. auto.
Qed.

Definition all_outputs (tx_hist : TxHistory) := (flat_map (fun tx => map (fun j => (stub tx, j)) (seq 0 (length (outputs (stub tx))))) (fst (split (tx_hist)))).
Definition output_spent tx_hist := (fun (tx_j : TxStub * Index) => let (tx, j) := tx_j in spent_output_dec tx_hist tx j).

Definition spent_unspent_outputs (tx_hist : TxHistory) : list (TxStub * Index) * list (TxStub * Index) :=
  partition (output_spent tx_hist) (all_outputs tx_hist).

(* Create a list of all (un)spent outputs in the tx_history *)
Definition UTXO (tx_hist : TxHistory) : list (TxStub * Index) := (snd (spent_unspent_outputs tx_hist)).
Definition STXO (tx_hist : TxHistory) : list (TxStub * Index) := (fst (spent_unspent_outputs tx_hist)).

(* In the following definitions, tx'_i is the transaction being redeemed and o_i is its output index *)
Definition redeemed_output_unspent tx_hist (tx'_i : TxStub) (o_i : Index) := In (tx'_i, o_i) (UTXO tx_hist).
Definition redeemed_output_spent tx_hist (tx'_i : TxStub) (o_i : Index) := In (tx'_i, o_i) (STXO tx_hist).

Lemma unspent_or_spent: forall tx_hist tx time o_i,
  In (tx, time) (tx_hist) ->
  o_i < length (outputs (stub tx)) ->
  let output := (stub tx, o_i) in
  In output (STXO tx_hist) \/ In output (UTXO tx_hist).
Proof.
  intros.
  set (outputs := all_outputs tx_hist).
  assert (partition (output_spent tx_hist) outputs = (STXO tx_hist, UTXO tx_hist)).
  unfold UTXO. unfold STXO. unfold spent_unspent_outputs. rewrite <- surjective_pairing. reflexivity.
  pose proof (elements_in_partition (output_spent tx_hist)).
  specialize (H2 outputs (STXO tx_hist) (UTXO tx_hist) H1 output). apply H2.
  clear H1 H2.
  unfold all_outputs in *. subst output outputs.
  apply in_flat_map. exists tx0. split.
  + apply in_split_l in H. intuition.
  + apply in_map. apply in_seq. omega.
Qed.

Lemma spent_not_unspent: forall tx_hist tx time o_i,
  In (tx, time) (tx_hist) ->
  o_i < length (outputs (stub tx)) ->
  let output := (stub tx, o_i) in
  In output (STXO tx_hist) -> ~ In output (UTXO tx_hist).
Proof.
  intros.
  set (outputs := all_outputs tx_hist).
  assert (partition (output_spent tx_hist) outputs = (STXO tx_hist, UTXO tx_hist)).
  unfold UTXO. unfold STXO. unfold spent_unspent_outputs. apply surjective_pairing.
  pose proof (partition_xor _ (output_spent tx_hist)).
  specialize (H3 outputs (STXO tx_hist) (UTXO tx_hist) H2 output). unfold not. apply H3; auto.
  clear H2 H3.
  unfold all_outputs in *. subst output outputs.
  apply in_flat_map. exists tx0. split.
  + apply in_split_l in H. intuition.
  + apply in_map. apply in_seq. omega.
Qed.

(** tx' is the transaction redeemed by the i-th input of tx *)
Definition redeemed_tx (tx_hist : TxHistory) (tx' tx : Tx) (i : Index) : Prop :=
  exists tx_redeemed, option_map (fun input => fst (fst input)) (tx.in(i)) = Some tx_redeemed
  /\ [tx'] = match_tx_hist_stub tx_hist tx_redeemed.

(* In the following definitions, tx'_i is the transaction being redeemed and tx is the redeeming transaction *)
Definition input_redeems_output tx_hist (tx'_i : Tx) (o_i : Index) (tx : Tx) (i : Index) (t : Time) := exists s_i v_i t'_i,
  time_tx_hist tx_hist (stub tx'_i) = Some t'_i /\
  tx'_i.out(o_i) = Some (s_i, v_i) /\
  redeems_output_dec (stub tx'_i) o_i t'_i v_i tx i t = true /\
  exists j, nth_error (tx_hist) j = Some (tx'_i, t'_i).


(* Need a function which gets the value of the jth output of a transaction. 0 for nonexistent output. *)
Definition get_output_value tx_stub j := nth j (map snd (outputs tx_stub)) 0.

(* The following function gets the value of ith input, which is the value of the output it is redeeming. *)
Definition get_input_value (input : TxStub * Index * Time) :=
  match input with
  | (stb, idx, _) => get_output_value stb idx
  end.

Definition sum_inputs (tx : TxStub) : Satoshi :=
  fold_left (fun v in_i => get_input_value in_i + v) (inputs tx) 0.

Definition sum_outputs (tx : TxStub) : Satoshi :=
  fold_left (fun v out_i => snd out_i + v) (outputs tx) 0.

(* The sum of values being output by t is less than the sum of outputs being redeemed by t *)
Definition nonincreasing_value (tx : TxStub) := sum_inputs tx >= sum_outputs tx.
(* Newly added transaction has to have a time greater or equal to the last time in the history. *)
Definition time_after_last (tx_hist : TxHistory) t := forall tx_hist' tx' t', tx_hist = tx_hist' ++ [(tx', t')] -> t' <= t.

(* Block-definition-independent height calculation by counting coinbases *)
Definition coinbase_height (tx_hist : TxHistory) : nat :=
  fold_left (fun bh tx => match tx with | coinbase _ _ => S bh | _ => bh end) (map stub (fst (split tx_hist))) 0.

(** Consistent update of a transaction history with a transaction *)
Definition is_consistent_update (tx_hist : TxHistory) (tx : Tx) (t : Time) :=
    (* coinbase *)
    (exists (bh : nat), exists (outputs : list (Exp * Satoshi)),
    stub tx = coinbase bh outputs /\
    time_after_last tx_hist t /\
    bh = coinbase_height tx_hist) \/
    (* nontrivial case *)
    (nonincreasing_value (stub tx) /\
    time_after_last tx_hist t /\

    inputs (stub tx) <> [] /\
    NoDup (map fst (inputs (stub tx))) /\

    forall (i : Index), i < length (inputs (stub tx)) ->
    exists (input : TxStub * Index * Time), tx.in(i) = Some input /\
    let tx'_i := fst (fst input) in
    let o_i := snd (fst input) in
    redeemed_output_unspent tx_hist tx'_i o_i /\
    exists (tx' : Tx), redeemed_tx tx_hist tx' tx i /\
    input_redeems_output tx_hist tx' o_i tx i t).


Inductive tx_history_consistent (tx_hist : TxHistory) : Prop :=
  | tx_hist_empty (TXH_EMPTY : tx_hist = []) : tx_history_consistent tx_hist
  | tx_hist_cons tx_hist' tx time
    (TXH_APPEND : tx_hist = tx_hist' ++ [(tx, time)])
    (TXH_UPDATE : is_consistent_update tx_hist' tx time)
    (BC'_CONS : tx_history_consistent tx_hist') : tx_history_consistent tx_hist.

Hint Constructors tx_history_consistent : core.

(** Lemma: in a consistent tx history, the inputs of a transaction point backwards
    to the output of some transaction in the tx history. *)
Lemma exists_preceding_output: forall tx_hist i,
  tx_history_consistent tx_hist ->

  (* allow the initial transaction since by consistency it can't have any inputs to begin with *)
  i < length tx_hist ->

  forall T_i time_i, Some (T_i, time_i) = nth_error tx_hist i ->

  forall (prev_tx: TxStub) (output_idx : nat) (relLock : Time) (input_idx : Index),
    T_i.in(input_idx) = Some (prev_tx, output_idx, relLock) ->

    exists j, j < i /\
      exists T_j time_j s v, Some (T_j, time_j) = nth_error tx_hist j /\
      stub T_j = prev_tx /\ T_j.out(output_idx) = Some (s, v) /\
      redeems_output_dec (stub T_j) output_idx time_j v T_i input_idx time_i = true.
Proof.
  intros tx_hist i H_tx_hist_cons H_i_range.
  generalize dependent i.
  induction H_tx_hist_cons.
  + (* Trivial case. The tx_history is empty, but we are required to prove only transactions
       after the first one have redeemed predecessors. Simply show that H_i_range is impossible. *)
    intros. rewrite TXH_EMPTY in H_i_range. simpl in H_i_range. omega.

  + intros i H_i_range T_i time_i H_index_i prev_tx output_idx relLock input_idx H_input.
    rename tx0 into tx_last, time into time_last.
    simpl in IHH_tx_hist_cons.

    (* Trivial facts about list lengths *)
    assert (length (tx_hist) = (length tx_hist') + 1) as H_len_plus_1 by (eapply length_app_1; eauto).
    assert (length tx_hist' < length (tx_hist)) as H_len_lt by omega.

    (* The tx_history was consistently updated with the last transaction. *)

    rename H_i_range into Hhi.

    (* The index i is either of a previously added transaction or the last one *)
    assert (i < length tx_hist' \/ i = length tx_hist') as H_i_range by omega.

    destruct H_i_range as [Hhi1 | Heq].
    {
      (* i < Datatypes.length tx_hist' => follows by IH *)
      assert (i < Datatypes.length tx_hist') as H_i_range by auto.
      clear Hhi H_len_plus_1 H_len_lt H_tx_hist_cons.

      specialize (IHH_tx_hist_cons i).
      apply IHH_tx_hist_cons with (T_i := T_i) (time_i := time_i) (input_idx := input_idx)
      (prev_tx := prev_tx) (output_idx := output_idx) (relLock := relLock) in H_i_range as H_goal; auto.

      (* Almost done, just fix the indexing part *)
      destruct H_goal as [j H]. destruct H as [Hji Hex].
      pose proof (lt_trans _ _ _ Hji Hhi1) as H_j_range.
      apply nth_error_app1 with (l' := [(tx_last, time_last)]) in H_j_range as H_nth_eq.
      rewrite <- TXH_APPEND in H_nth_eq.
      rewrite <- H_nth_eq in *.
      exists j. auto.
      apply nth_error_app1 with (l' := [(tx_last, time_last)]) in Hhi1 as H_nth_eq.
      rewrite <- TXH_APPEND in H_nth_eq.
      rewrite <- H_nth_eq in *. exact H_index_i.
    }
    {
      (* i = Datatypes.length tx_hist' => follows by input_redeems_output *)
      (* Prove that tx_last (last added transaction) = T_i (transaction at index i) *)
      pose proof (list_last (tx_hist) (tx_hist') i (T_i, time_i) (tx_last, time_last) Heq H_index_i TXH_APPEND)
           as H_tx_last_Ti.
      inversion H_tx_last_Ti. rewrite H0 in *. rewrite H1 in *. clear H_tx_last_Ti H0 H1.

      clear IHH_tx_hist_cons Hhi H_len_plus_1 H_len_lt H_tx_hist_cons.

      (* Analyze how the update happened *)
      destruct TXH_UPDATE as [H_coin | H_upd].
      {
        (* The tx_history was updated with a coinbase tx which has no inputs, so nothing to prove *)
        destruct H_coin as [block_height [output [H_coin _]]].
        exfalso.
        unfold inputs in H_input. rewrite H_coin in H_input.
        apply nth_error_In in H_input. assumption.
      }
      {
        (* Use the consistent update hypothesis *)
        simpl in H_upd.
        do 4 destruct H_upd as [_ H_upd].
        destruct H_upd with (i := input_idx) as [input H_upd']. clear H_upd.
        (* First prove that n is indeed an input index *)
        { apply nth_error_Some. unfold Index in *. congruence. }

        destruct H_upd' as [H_input' H_upd'].
        destruct H_upd' as [_ H_upd'].
        destruct H_upd' as [tx' H_upd'].
        (* Equate the input with the tuple finally *)
        unfold Index in *. rewrite -> H_input in H_input'.
        inversion H_input' as [H_input'']. rewrite <- H_input'' in *. simpl in *.
        clear H_input' H_input''.
        (* Recover the important condition (input_redeems_output) *)
        destruct H_upd' as [_ H_tx_last_redeems_output].

        (* Recover the witness index j *)
        destruct H_tx_last_redeems_output as [s H].
        destruct H as [v H].
        destruct H as [t' H].
        decompose [and] H.
        destruct H4 as [j H_index_j].
        clear H H0. rename H1 into H_stub, H2 into H_output.
        assert (H_redeems := H_stub).
        (* Analyze the algorithm for deciding redeeming to recover equalities about arguments *)
        unfold redeems_output_dec in H_stub.
        unfold Index in H_stub.
        rewrite -> H_input in H_stub.
        do 4 ( rewrite andb_true_iff in H_stub; destruct H_stub as [H_stub _] ).
        apply TxStub_beq_eq in H_stub.
        unfold Index in *.

        exists j. split.
        {
          (* Prove that j precedes i *)
          rewrite Heq. apply nth_error_Some. congruence.
        }
        {
          (* Prove the main result about the redeemed transaction and output *)
          exists tx'. exists t'. exists s. exists v. repeat split; auto.
          symmetry. rewrite <- H_index_j. rewrite TXH_APPEND. apply nth_error_app1.
          apply nth_error_Some. congruence.
        }
      }
    }
Qed.

Definition tx_hist_prefix_to (i : Index) (tx_hist : TxHistory) := (firstn (i+1) (tx_hist)).

(** Lemma: all prefixes of a consistent transaction history are themselves consistent *)
Lemma tx_hist_prefix_consistent: forall tx_hist1 tx_hist2 suff,
  tx_hist2 = tx_hist1 ++ suff ->
  tx_history_consistent tx_hist2 -> tx_history_consistent tx_hist1.
Proof.
  intros tx_hist1 tx_hist2 suff H_append.
  generalize dependent tx_hist1. generalize dependent tx_hist2.
  induction suff using @rev_ind; intros.
  {
    rewrite app_nil_r in H_append. subst. auto.
  }
  {
    remember (tx_hist1 ++ suff) as tx_hist1' eqn: H0.
    rewrite app_assoc in H_append. rewrite <- H0 in H_append.

    apply IHsuff in H0; auto.

    inversion H.
    + rewrite TXH_EMPTY in *.
      pose proof (app_cons_not_nil tx_hist1' [] x).
      intuition.
    + rewrite H_append in TXH_APPEND. apply app_inj_tail in TXH_APPEND.
      destruct TXH_APPEND. subst. auto.
  }
Qed.

(** Lemma: all prefixes of a consistent transaction history are themselves consistent *)
Lemma tx_hist_prefix_consistent_index:
  forall tx_hist i, tx_history_consistent tx_hist -> tx_history_consistent (tx_hist_prefix_to i tx_hist).
Proof.
  intros.
  unfold tx_hist_prefix_to.
  pose proof (firstn_prefix (tx_hist) (i + 1)).
  destruct X as [suff H_append].
  remember (firstn (i + 1) (tx_hist)) as tx_hist_pref.
  rename Heqtx_hist_pref into H_txlist.
  symmetry in H_append.
  apply (tx_hist_prefix_consistent tx_hist_pref tx_hist suff); auto.
Qed.

Lemma spent_update: forall tx_hist tx_hist' tx time,
  tx_hist = tx_hist' ++ [(tx, time)] ->
  incl (STXO tx_hist') (STXO tx_hist).
Proof.
  intros.
  rename H into H_append.
  rewrite H_append.
  unfold STXO. unfold spent_unspent_outputs.
  unfold output_spent. unfold all_outputs.
  intuition.

  unfold incl. intros.

  rewrite split_app_fst. rewrite flat_map_concat_map.
  rewrite map_app. rewrite concat_app. simpl (fst (split _)).
  rewrite partition_app_fst.
  simpl. rewrite app_nil_r.
  apply in_or_app. left.
  rewrite <- flat_map_concat_map.
  pose proof (spent_output_monotonic) as H_mono.
  specialize H_mono with (tx_hist1 := tx_hist') (tx_hist2 := tx_hist) (suff := [(tx0, time)]).
  specialize (H_mono H_append).

  generalize H.
  apply partition_monotonic.
  unfold monotonic.
  destruct a0.
  subst.
  apply H_mono.
Qed.


Lemma spent_update': forall tx_hist tx_hist' tx time
  (BCONS: tx_history_consistent tx_hist) (BAPP: tx_hist = tx_hist' ++ [(tx, time)]),
  incl (fst (split (inputs (stub tx)))) (STXO tx_hist).
Proof.
  intros.
  intros input IN.
  unfold STXO, spent_unspent_outputs.
  pose proof (partition_filter _ (all_outputs tx_hist) (output_spent tx_hist)) as FILT.
  destruct FILT as [F1 _].
  unfold Index in *.
  rewrite <- F1.
  clear F1.

  set (len := length tx_hist').
  assert (len < length (tx_hist)) as QQ
    by (rewrite BAPP; rewrite app_length; simpl; omega).

  assert (Some (tx0, time) = nth_error (tx_hist) len) as QQQ.
  {
    subst len; rewrite BAPP.
    rewrite nth_error_app2; intuition.
    rewrite Nat.sub_diag; reflexivity.
  }
  pose proof exists_preceding_output tx_hist len BCONS QQ tx0 time QQQ as PRECEEDING.
  clear QQ QQQ.

  remember BCONS as BCONS_REM; clear HeqBCONS_REM.
  destruct BCONS.
  - rewrite TXH_EMPTY in BAPP; apply app_cons_not_nil in BAPP; exfalso; trivial.
  - assert (tx_hist'0 = tx_hist' /\ tx1 = tx0 /\ time0 = time) as EQ.
    {
        rewrite TXH_APPEND in BAPP; apply list_app_eq in BAPP.
        destruct BAPP; inversion H0; subst. auto.
    }
    destruct EQ as [H0 H1]; destruct H1; subst; clear BAPP.
    set (tx_hist := (tx_hist' ++ _)) in *.

    unfold is_consistent_update in TXH_UPDATE; destruct TXH_UPDATE as [COIN | CONSUP];
    [exfalso;
      destruct COIN as [bh [output [COIN _]]];
      rewrite COIN in IN; auto|].
     apply In_nth_error in IN; destruct IN as [idx SOME].

     destruct CONSUP as [C1 [C2 [_ [_ C3]]]].

     assert (idx < length (inputs (stub tx0))) as LEN.
     {
       assert (length (fst (split (inputs (stub tx0)))) = length (inputs (stub tx0)))
        by apply split_length_l.
       rewrite <- H; apply nth_error_Some.
       intro CONTRA; unfold Index in *; congruence.
     }
     specialize (C3 idx LEN).

     destruct C3 as [input2 [T0_has_input [UNSPENT EXISTS]]].
     destruct EXISTS as [tx_being_redeemed [RED_PROP1 RED_PROP2]].
     destruct input2 as [[input2 idx2] time2].
     specialize (PRECEEDING input2 idx2 time2 idx T0_has_input).

     destruct PRECEEDING as [idxjj [LEN_idxjj EXX]].
     destruct EXX as [txx [time_j [s [v PROPS]]]].

     assert ((input2,idx2) = input).
     {
      clear -T0_has_input SOME LEN.
      unfold nth_error in T0_has_input.
      fold (nth_error (inputs (stub tx0)) idx) in T0_has_input.
      destruct tx0; simpl in *.
      destruct stub0; simpl in *.
      apply map_nth_error with (f:=fst) in T0_has_input.
      simpl in *.
      rewrite map_split in T0_has_input.
      unfold Index in *.
      rewrite T0_has_input in SOME.
      inversion SOME; intuition.
      apply nth_error_In in SOME. inversion SOME.
     }
     destruct input as [input o_i].
     inversion H; clear H; simpl in *; subst.
		 destruct PROPS as [P1 [P2 [P3 P4]]].
     assert (EE: stub txx = input) by intuition; subst; clear EE.
		 apply filter_In; split.
		 {
       unfold all_outputs.
       apply in_flat_map.
       exists txx.
       split.
       {
           assert (In (fst (txx, time_j)) (fst (split (tx_hist)))) as WWW
             by (apply in_split_l; symmetry in P1; apply nth_error_In in P1; auto).
           simpl in WWW; auto.
       }
       apply in_map_iff; exists o_i; intuition.
       apply in_seq; intuition.
       apply nth_error_Some; congruence.
     }
     unfold output_spent, spent_output_dec.
     apply existsb_exists.
     exists (txx, time_j); split.
     { symmetry in P1; apply nth_error_In in P1; auto. }
     rewrite andb_true_iff; split. simpl. apply TxStub_eq_beq.
     apply existsb_exists.
     exists (tx0, time); split.
     { subst tx_hist; apply in_app_iff; right; intuition. }
     simpl.
     unfold redeems_any.
     rewrite P3.
     apply existsb_exists.
     exists (idx, (stub txx, o_i,time2)).
     split; intuition.
     apply enumerate_list_nth in T0_has_input.
     apply nth_error_In in T0_has_input.
     auto.
Qed.

Lemma spent_remains_spent2: forall tx_hist1 tx_hist2 suff,
  tx_hist2 = tx_hist1 ++ suff ->
  incl (STXO tx_hist1) (STXO tx_hist2).
Proof.
  intros.
  generalize dependent tx_hist2.
  generalize dependent tx_hist1.
  induction suff using @rev_ind; intros.
  {
    rewrite app_nil_r in H. subst. intuition.
  }
  {
    set (tx_hist1' := tx_hist1 ++ suff).
    assert (tx_hist1' = tx_hist1 ++ suff) by intuition.
    rewrite app_assoc in H. rewrite <- H0 in H.
    apply IHsuff in H0.

    destruct x.
    apply spent_update in H. eapply incl_tran; eauto.
  }
Qed.

Lemma spent_remains_spent: forall tx_hist tx_hist' tx_hist_future tx time input (TXH_CONS : tx_history_consistent tx_hist),
  tx_hist = tx_hist' ++ [(tx, time)] ->
  In input (inputs (stub tx)) ->
  let tx_redeemed := fst (fst input) in
  let tx_redeemed_output_index := snd (fst input) in
  is_prefix_of (tx_hist) (tx_hist_future) ->
  redeemed_output_spent tx_hist_future tx_redeemed tx_redeemed_output_index.
Proof.
  intros.
  destruct input as [tx_o_i relLock].
  destruct tx_o_i as [tx' tx'_o_i].
  simpl in *. subst tx_redeemed tx_redeemed_output_index.
  assert (H_append := H).
  apply spent_update in H.
  pose proof (spent_update' tx_hist tx_hist' tx0 time TXH_CONS H_append).
  unfold redeemed_output_spent.
  unfold incl in H1.

  apply in_split_l in H0. simpl in H0.
  apply H1 in H0. clear H1.
  destruct X as [suff H_append'].
  symmetry in H_append'.
  pose proof (spent_remains_spent2 tx_hist tx_hist_future suff H_append'). clear H_append'.
  intuition.
Qed.

(** Theorem: No double spending (distinct tx case) *)
Theorem no_double_spending_distinct: forall tx_hist,
  tx_history_consistent tx_hist ->

  forall i j T_i time_i T_j time_j, i < length tx_hist -> j < length tx_hist -> j < i ->
  Some (T_i, time_i) = nth_error tx_hist i ->
  Some (T_j, time_j) = nth_error tx_hist j ->

    forall input_of_ith input_of_jth,
    In input_of_ith (inputs (stub T_i)) ->
    In input_of_jth (inputs (stub T_j)) ->
    fst input_of_ith <> fst input_of_jth.
Proof.
  intros.
  pose proof (tx_hist_prefix_consistent_index tx_hist i H) as H_prefix_i.
  pose proof (tx_hist_prefix_consistent_index tx_hist j H) as H_prefix_j.
  unfold tx_hist_prefix_to in *.

  rewrite <- (nth_error_firstn j (tx_hist) H1) in H4.
  inversion H_prefix_j.
  { rewrite TXH_EMPTY in H4. symmetry in H4. apply nth_error_In in H4. inversion H4. }
  rename tx0 into T_j', time into time_j'.
  simpl in TXH_APPEND. assert ((j + 1) <= length (tx_hist)) by omega.
  pose proof (firstn_length_le (tx_hist) H7).
  assert (length (firstn (j + 1) (tx_hist)) = (length tx_hist') + 1) as H_len_plus_1 by (eapply length_app_1; eauto).
  assert (j = length tx_hist') by omega. clear H_len_plus_1.
  remember (firstn (j + 1) (tx_hist)) as prefix_j.
  pose proof (list_last prefix_j tx_hist' j (T_j, time_j) (T_j', time_j') H9 H4 TXH_APPEND).
  symmetry in H10. inversion H10. clear H9. subst. clear H7 H8 H10.
  rename TXH_APPEND into TXH_APPEND_j, TXH_UPDATE into TXH_UPDATE_j, BC'_CONS into BC'_CONS_j.
  rename tx_hist' into tx_hist'_j.

  rewrite <- (nth_error_firstn i (tx_hist) H0) in H3.
  inversion H_prefix_i.
  { simpl in *. rewrite TXH_EMPTY in H3. symmetry in H3. apply nth_error_In in H3. inversion H3. }
  rename tx0 into T_i', time into time_i'.
  simpl in TXH_APPEND. assert ((i + 1) <= length (tx_hist)) by omega.
  pose proof (firstn_length_le (tx_hist) H7).
  assert (length (firstn (i + 1) (tx_hist)) = (length tx_hist') + 1) as H_len_plus_1 by (eapply length_app_1; eauto).
  assert (i = length tx_hist') by omega. clear H_len_plus_1.
  remember (firstn (i + 1) (tx_hist)) as prefix_i.
  pose proof (list_last prefix_i tx_hist' i (T_i, time_i) (T_i', time_i') H9 H3 TXH_APPEND).
  symmetry in H10. inversion H10. clear H9. subst. clear H7 H8 H10.
  rename TXH_APPEND into TXH_APPEND_i, TXH_UPDATE into TXH_UPDATE_i, BC'_CONS into BC'_CONS_i.
  rename tx_hist' into tx_hist'_i.

  destruct TXH_UPDATE_j as [H_coin | H_upd_j].
  {
    destruct H_coin as [bh [output [H_coin _]]].
    rewrite H_coin in H6.
    inversion H6.
  }
  do 4 destruct H_upd_j as [_ H_upd_j].
  assert (H_input_j := H6).
  apply In_nth_error in H6. destruct H6 as [input_j_index].
  specialize H_upd_j with (i := input_j_index).
  destruct H_upd_j as [input_j H_upd_j]. apply nth_error_Some. congruence. rewrite H6 in *. clear H6.
  destruct H_upd_j as [H_input_j_eq H_upd_j]. inversion H_input_j_eq. subst.
  simpl in H_upd_j. clear H_input_j_eq.
  destruct H_upd_j as [H_UTXO_j _].

  destruct TXH_UPDATE_i as [H_coin | H_upd_i].
  {
    destruct H_coin as [bh [output [H_coin _]]].
    rewrite H_coin in H5.
    inversion H5.
  }
  do 4 destruct H_upd_i as [_ H_upd_i].
  assert (H_input_i := H5).
  apply In_nth_error in H5. destruct H5 as [input_i_index].
  specialize H_upd_i with (i := input_i_index).
  destruct H_upd_i as [input_i H_upd_i]. apply nth_error_Some. congruence. rewrite H5 in *. clear H5.
  destruct H_upd_i as [H_input_i_eq H_upd_i]. inversion H_input_i_eq. subst.
  simpl in H_upd_i. clear H_input_i_eq.
  destruct H_upd_i as [H_UTXO_i _].

  pose proof (spent_remains_spent) as H_spent.
  specialize (H_spent (tx_hist_prefix_to j tx_hist)).
  specialize (H_spent tx_hist'_j tx_hist'_i T_j time_j input_j).

  pose proof (H_spent H_prefix_j TXH_APPEND_j H_input_j) as H_spent.
  simpl in H_spent.

  intro H_contra.

  pose proof (spent_not_unspent) as H_xor.
  specialize (H_xor tx_hist'_i).
  pose proof (exists_preceding_output) as H_output.
  specialize (H_output (tx_hist_prefix_to i tx_hist) i H_prefix_i).
  pose proof (@firstn_length_le _ (tx_hist) (i + 1)).
  assert (length (firstn (i + 1) (tx_hist)) = i + 1) as H_length by omega.
  assert (i < length (firstn (i + 1) (tx_hist))) by omega.
  specialize (H_output H6 T_i time_i H3). clear H5 H6.
  destruct input_i as [p relLock_input_i]. destruct p as [T' T'_o_i].
  specialize (H_output T' T'_o_i relLock_input_i).
  apply In_nth_error in H_input_i.
  destruct H_input_i as [input_i_idx H_input_i].
  specialize (H_output input_i_idx H_input_i).

  destruct H_output as [k H_output].
  destruct H_output as [H_k_lt_i H_output].
  destruct H_output as [T_k H_output].
  destruct H_output as [time_k H_output].
  specialize (H_xor T_k time_k T'_o_i).

  destruct H_output as [s_k H_output].
  destruct H_output as [v_k H_output].
  decompose [and] H_output. clear H_output.
  rename H6 into H_output, H5 into H_T_k_in_tx_hist, H7 into H_T_k_eq.
  rewrite <- H_T_k_eq in *. clear H_T_k_eq.
  symmetry in H_T_k_in_tx_hist.
  simpl in H_T_k_in_tx_hist.
  apply length_app_1 in TXH_APPEND_i as H_tx_hist'_i_length.
  rewrite H_length in H_tx_hist'_i_length.
  assert (length (tx_hist'_i) = i) as Heq_i by omega.
  rewrite <- Heq_i in H_k_lt_i.
  unfold tx_hist_prefix_to in *.
  rewrite TXH_APPEND_i in H_T_k_in_tx_hist.
  pose proof (@nth_error_app1 _ _ [(T_i, time_i)] k H_k_lt_i).
  rewrite H5 in H_T_k_in_tx_hist.

  apply nth_error_In in H_T_k_in_tx_hist.
  specialize (H_xor H_T_k_in_tx_hist).

  assert (T_k.out(T'_o_i) <> None) by congruence.
  apply nth_error_Some in H6.
  specialize (H_xor H6). simpl in H_xor, H_UTXO_i.
  unfold redeemed_output_unspent in H_UTXO_i.

  apply H_xor; auto. clear H_xor.
  rewrite <- H_contra in *. simpl in H_spent. unfold redeemed_output_spent in H_spent.

  apply H_spent.
  {
    simpl.

    assert (firstn (j + 1) (tx_hist) = firstn (j + 1) (tx_hist'_i)).
    {
      pose proof (firstn_firstn (tx_hist) (j + 1) (i + 1)).
      simpl in H7. rewrite min_l in H7; try omega. rewrite TXH_APPEND_i in H7.
      rewrite <- H7. rewrite firstn_app.

      assert (length (firstn (i + 1) (tx_hist)) = length (tx_hist'_i) + 1) by (eapply length_app_1; eauto).
      assert (length (firstn (i + 1) (tx_hist)) = i + 1) by (apply firstn_length_le; omega).
      assert (length (tx_hist'_i) = i) by omega. rewrite H11.
      assert (j + 1 - i = 0) by omega. rewrite H12. simpl. intuition.
    }

    rewrite H7. apply firstn_prefix.
  }
Qed.

(** Theorem: No double spending *)
Theorem no_double_spending: forall tx_hist,
  tx_history_consistent tx_hist ->

  forall i j T_i time_i T_j time_j, i < length tx_hist -> j < length tx_hist ->
  Some (T_i, time_i) = nth_error tx_hist i ->
  Some (T_j, time_j) = nth_error tx_hist j ->

    forall input_of_ith input_of_jth input_of_ith_index input_of_jth_index,
    nth_error (inputs (stub T_i)) input_of_ith_index = Some input_of_ith ->
    nth_error (inputs (stub T_j)) input_of_jth_index = Some input_of_jth ->
    (i, input_of_ith_index) <> (j, input_of_jth_index) ->
    fst input_of_ith <> fst input_of_jth.
Proof.
  intros.
  apply nth_error_In in H4 as H_In_ith.
  apply nth_error_In in H5 as H_In_jth.
  assert (j < i \/ i < j \/ i = j) by (omega).
  decompose [or] H7.
  apply (no_double_spending_distinct tx_hist H i j T_i time_i T_j time_j); auto.

  intro. symmetry in H8. generalize H8.
  apply (no_double_spending_distinct tx_hist H j i T_j time_j T_i time_i H1 H0 H9 H3 H2 input_of_jth input_of_ith); auto.

  subst. rewrite <- H3 in H2. inversion H2. clear H2. subst. clear H7.
  rename input_of_ith into input1, input_of_jth into input2.
  induction H.
  {
    rewrite TXH_EMPTY in *. symmetry in H3. apply nth_error_In in H3. inversion H3.
  }
  {
    apply length_app_1 in TXH_APPEND as Hlen. rewrite Hlen in *.
    assert (j < Datatypes.length tx_hist' \/ j = Datatypes.length tx_hist') by omega.
    destruct H2.
    + apply IHtx_history_consistent; auto.
      rewrite TXH_APPEND in H3. rewrite nth_error_app1 in H3; auto.
    + clear IHtx_history_consistent H0 H1. subst.
      rewrite nth_error_app2 in H3; auto.
      rewrite minus_diag in H3. simpl in H3. inversion H3. subst.
      clear H3 H Hlen.

      apply (map_nth_error fst) in H4.
      apply (map_nth_error fst) in H5.
      set (ins := map fst (inputs (stub tx0))) in *.

      apply (NoDup_distinct _ ins input_of_ith_index input_of_jth_index); subst ins; auto.
      destruct TXH_UPDATE as [H | H].
      - destruct H as [bh [output [H_coin _]]]. rewrite H_coin. simpl. apply NoDup_nil.
      - destruct H as [_ [_ [_ [Hnodup _]]]]. assumption.
  }
Qed.

(* Example of a double spending transaction making the tx_history inconsistent *)

Section InconsistencyExample.

Let key := 1777%nat.
Let my_SK := key_sk key.
Let my_PK := key_pk key.

Let scriptPubKey :=
  e_and (e_equal (e_hash (e_const (sv_int 1777))) (e_hash (e_var x))) (e_versig [my_PK] [e_var y]).
Let genesis_TxStub := coinbase 0 [(scriptPubKey, 100%nat)].
Let genesis_Tx := tx genesis_TxStub [].

Let offender_TxStub := tx_stub [(genesis_TxStub, 0, 0); (genesis_TxStub, 0, 1)] [] 0.
Let offender_scriptSig := [sv_int 1777; sv_sig offender_TxStub my_SK m_ss 0%nat].
Let offender_Tx := tx offender_TxStub [offender_scriptSig; offender_scriptSig].

Goal verifies offender_Tx 0%nat scriptPubKey /\ verifies offender_Tx 1%nat scriptPubKey.
Proof. split; constructor; reflexivity. Qed.

Let offender_tx_hist := [(genesis_Tx, 0); (offender_Tx, 1)].

Goal ~ tx_history_consistent offender_tx_hist.
Proof.
  unfold offender_tx_hist.
  intro.

  destruct H.
  {
    inversion TXH_EMPTY.
  }
  {
    simpl in *.
    change ([(genesis_Tx, 0); (offender_Tx, 1)]) with ([(genesis_Tx, 0)] ++ [(offender_Tx, 1)]) in TXH_APPEND;
    apply app_inj_tail in TXH_APPEND;
    inversion TXH_APPEND;
    inversion H1; subst; clear H1 TXH_APPEND.

    destruct TXH_UPDATE as [H_coin | H_tx].
    - destruct H_coin as [bh [output [H_coin _]]]; discriminate.
    - decompose [and] H_tx; simpl in *; inversion_clear H3; intuition.
  }
Qed.

End InconsistencyExample.


(* Transaction uniqueness *)

Definition coinbase_height' (tx_hist : list TxStub) : nat :=
  fold_left (fun bh tx => match tx with | coinbase _ _ => S bh | _ => bh end) tx_hist 0.

Lemma coinbase_height_alt : forall tx_hist,
  coinbase_height tx_hist = coinbase_height' (map stub (fst (split tx_hist))).
Proof.
  auto.
Qed.

Lemma coinbase_height'_monotone : forall tx_hist suff, coinbase_height' tx_hist <= coinbase_height' (tx_hist ++ suff).
Proof.
  intros.
  induction suff as [| stub] using rev_ind.
  {
    rewrite app_nil_r; reflexivity.
  }
  {
    rewrite app_assoc.
    set (tx_hist' := tx_hist ++ suff) in *.
    transitivity (coinbase_height' (tx_hist')); auto; clear IHsuff.
    unfold coinbase_height'; rewrite fold_left_app;
    fold (coinbase_height' tx_hist'); simpl.
    destruct stub; auto.
  }
Qed.

Lemma coinbase_height_monotone : forall tx_hist suff, coinbase_height tx_hist <= coinbase_height (tx_hist ++ suff).
Proof.
  intros;
  rewrite !coinbase_height_alt, <- !map_split, !map_map, map_app; apply coinbase_height'_monotone.
Qed.

(* A slightly different statement than the one below, for convenience *)
Theorem transaction_uniqueness_strong :
  forall tx_hist : TxHistory, tx_history_consistent tx_hist ->
  let tx_hist_stubs := map stub (fst (split tx_hist)) in
  forall (i j : nat) (T_i T_j : TxStub),
    i < Datatypes.length tx_hist_stubs ->
    j < Datatypes.length tx_hist_stubs ->
    Some T_i = nth_error tx_hist_stubs i ->
    Some T_j = nth_error tx_hist_stubs j ->
    T_i = T_j -> i = j.
Proof.
  intros.
  subst tx_hist_stubs; rewrite <- map_split, map_map in *;
  assert (H_i_len := H0); assert (H_j_len := H1); rewrite map_length in H_i_len, H_j_len.
  set (proj := (fun x : Tx * Time => stub (fst x))) in *.

  destruct (tx_hist_prefix_consistent_index tx_hist i H);
  [ unfold tx_hist_prefix_to in *;
  rewrite <- nth_error_firstn, firstn_map in H2; auto;
  rewrite TXH_EMPTY in *; simpl in *;
  symmetry in H2; apply nth_error_In in H2; contradiction |].

  destruct (tx_hist_prefix_consistent_index tx_hist j H);
  [ unfold tx_hist_prefix_to in *;
  rewrite <- nth_error_firstn, firstn_map in H3; auto;
  rewrite TXH_EMPTY in *; simpl in *;
  symmetry in H3; apply nth_error_In in H3; contradiction |].
  assert (H2' := H2); assert (H3' := H3).
  unfold tx_hist_prefix_to in *; rewrite <- nth_error_firstn, firstn_map in H2', H3'; auto.

  assert (i + 1 = Datatypes.length (firstn (i + 1) (map proj tx_hist))) as H_i1
  by (rewrite firstn_length_le; auto; omega);
  apply (f_equal (map proj)) in TXH_APPEND; rewrite <- firstn_map, map_app in TXH_APPEND;
  assert (i = Datatypes.length (map proj tx_hist')) as H_i by
  (rewrite TXH_APPEND, app_length in *; simpl in *; omega);
  rewrite firstn_map in TXH_APPEND;
  pose proof (list_last _ _ _ _ _ H_i H2' TXH_APPEND) as H_T1; inversion H_T1; clear H_T1 H_i H2'.

  assert (j + 1 = Datatypes.length (firstn (j + 1) (map proj tx_hist))) as H_j1
  by (rewrite firstn_length_le; auto; omega);
  apply (f_equal (map proj)) in TXH_APPEND0; rewrite <- firstn_map, map_app in TXH_APPEND0;
  assert (j = Datatypes.length (map proj tx_hist'0)) as H_j by
  (rewrite TXH_APPEND0, app_length in *; simpl in *; omega);
  rewrite firstn_map in TXH_APPEND0;
  pose proof (list_last _ _ _ _ _ H_j H3' TXH_APPEND0) as H_T2; inversion H_T2; clear H_T2 H_j H3'.

  subst proj. simpl in H5, H6.
  assert (i = j \/ j < i \/ i < j) as H_cases by omega; destruct H_cases; auto; exfalso.

  destruct TXH_UPDATE  as [[bh1 [outputs1 [H_coin1 [_ H_uniq1]]]] | [_ [_ [H_inputs1 _]]]];
  destruct TXH_UPDATE0 as [[bh2 [outputs2 [H_coin2 [_ H_uniq2]]]] | [_ [_ [H_inputs2 _]]]];
  try (rewrite coinbase_height_alt, <- map_split, map_map in *);
  simpl in *; set (proj := (fun x : Tx * Time => stub (fst x))) in *.
  rewrite <- H5, <- H6 in *; clear H5 H6.
  {
    destruct H7.
    - rewrite H4 in *; clear H4;
      rewrite H_coin2 in H_coin1; inversion H_coin1; clear - H0 H1 H5 H6 TXH_APPEND TXH_APPEND0 H_coin2 H_uniq1 H_uniq2.

      assert (is_prefix_of (map proj tx_hist'0 ++ [T_j]) (map proj tx_hist'))
      by (unfold is_prefix_of; rewrite <- TXH_APPEND0; fold (is_prefix_of (map proj (firstn (j + 1) tx_hist)) (map proj tx_hist'));
      rewrite <- firstn_map in *;
      apply firstn_app_one in TXH_APPEND; auto;
      replace (j + 1) with (min (j + 1) i); [
        rewrite <- firstn_firstn; rewrite TXH_APPEND; apply firstn_prefix |
        rewrite min_l; omega ]);
      destruct X as [suff]; rewrite <- e in *.

      pose proof coinbase_height'_monotone as H;
      specialize (H (map proj tx_hist'0 ++ [T_j]) suff) as H_above;
      specialize (H (map proj tx_hist'0) [T_j]) as H_below;
      assert (coinbase_height' (map proj tx_hist'0) = coinbase_height' (map proj tx_hist'0 ++ [T_j])) as H_false by omega;
      clear - H_false H_coin2.

      subst;
      unfold coinbase_height' in H_false;
      rewrite fold_left_app in H_false;
      fold (coinbase_height' (map proj tx_hist'0)) in H_false; simpl in H_false; omega.

    - rewrite <- H4 in *; clear H4;
      rewrite H_coin1 in H_coin2; inversion H_coin2; clear - H0 H1 H5 H6 TXH_APPEND TXH_APPEND0 H_coin1 H_uniq1 H_uniq2.

      assert (is_prefix_of (map proj tx_hist' ++ [T_i]) (map proj tx_hist'0))
      by (unfold is_prefix_of; rewrite <- TXH_APPEND; fold (is_prefix_of (map proj (firstn (i + 1) tx_hist)) (map proj tx_hist'0));
      rewrite <- firstn_map in *;
      apply firstn_app_one in TXH_APPEND0; auto;
      replace (i + 1) with (min (i + 1) j); [
        rewrite <- firstn_firstn; rewrite TXH_APPEND0; apply firstn_prefix |
        rewrite min_l; omega ]);
      destruct X as [suff]; rewrite <- e in *.

      pose proof coinbase_height'_monotone as H;
      specialize (H (map proj tx_hist' ++ [T_i]) suff) as H_above;
      specialize (H (map proj tx_hist') [T_i]) as H_below;
      assert (coinbase_height' (map proj tx_hist') = coinbase_height' (map proj tx_hist' ++ [T_i])) as H_false by omega;
      clear - H_false H_coin1.

      subst;
      unfold coinbase_height' in H_false;
      rewrite fold_left_app in H_false;
      fold (coinbase_height' (map proj tx_hist')) in H_false; simpl in H_false; omega.
  }
  {
    subst;
    rewrite H6 in *.
    rewrite H_coin1 in H_inputs2; contradiction.
  }
  {
    subst;
    rewrite H6 in *.
    rewrite H_coin2 in H_inputs1; contradiction.
  }
  {
    simpl in *.
    symmetry in H2, H3.
    apply nth_error_map_iff in H2; destruct H2 as [[tx0' time'] []].
    apply nth_error_map_iff in H3; destruct H3 as [[tx1' time0'] []].
    symmetry in H8, H9.
    destruct H7.
    - pose proof (no_double_spending_distinct tx_hist H i j tx0' time' tx1' time0' H_i_len H_j_len H7 H8 H9).
      rewrite <- H4 in *; clear H4.
      subst proj; subst; rewrite <- H6 in *; simpl in *; rewrite <- H3 in *.
      enough (exists input_of_ith, In input_of_ith (inputs (stub tx1'))).
      destruct H2 as [i1].
      eapply (H10 i1 i1 H2 H2); auto.

      rewrite H5 in *; apply exists_last in H_inputs1; destruct H_inputs1 as [inputs1' [i1 H_append1]];
      exists i1; rewrite H_append1; intuition.
    - pose proof (no_double_spending_distinct tx_hist H j i tx1' time0' tx0' time' H_j_len H_i_len H7 H9 H8).
      rewrite <- H4 in *; clear H4.
      subst proj; subst; rewrite <- H6 in *; simpl in *; rewrite <- H3 in *.
      enough (exists input_of_ith, In input_of_ith (inputs (stub tx1'))).
      destruct H2 as [i1];
      eapply (H10 i1 i1 H2 H2); auto.

      rewrite H5 in *; apply exists_last in H_inputs1; destruct H_inputs1 as [inputs1' [i1 H_append1]];
      exists i1; rewrite H_append1; intuition.
  }
Qed.

(** Theorem: transaction uniqueness *)
Theorem transaction_uniqueness :
  forall tx_hist, tx_history_consistent tx_hist ->
  forall i j T_i time_i T_j time_j, i < length tx_hist -> j < length tx_hist ->
    Some (T_i, time_i) = nth_error tx_hist i ->
    Some (T_j, time_j) = nth_error tx_hist j ->
    stub T_i = stub T_j -> i = j.
Proof.
  intros;
  apply (transaction_uniqueness_strong _ H i j (stub T_i) (stub T_j)); auto;
  try (rewrite map_length, split_length_l; auto);
  rewrite <- map_split, map_map;
  match goal with
  | [H : context[?T] |- context[?T]] => symmetry in H; symmetry; eapply map_nth_error in H; exact H
  end.
Qed.

(* Total UTXO value <= total coinbase value *)

(* sum of all unspent values in the tx history *)
Definition UTXO_value (tx_hist : TxHistory) : Satoshi :=
  fold_left (fun (acc : Satoshi) (output : TxStub * Index) =>
    let (tx, output_idx) := output in
    acc + match (nth_error (outputs tx) output_idx) with
    | Some (_, v) => v
    | _ => 0
    end) (UTXO tx_hist) 0.

(* sum of all value introduced in coinbase tx-s in the tx history *)
Definition coinbase_value (tx_hist : TxHistory) : Satoshi :=
  fold_left (fun (acc : Satoshi) (tx : TxStub) =>
    acc + match tx with
    | coinbase _ _ as c => sum_outputs c
    | _ => 0
    end) (map stub (fst (split tx_hist))) 0.

(** Lemma: no transaction may redeem its own outputs *)
Lemma no_self_redeem : forall tx output_idx time1 time2,
  redeems_any (stub tx) output_idx time1 tx time2 = false.
Proof.
  intros.
  destruct tx0 as [[] witnesses]; simpl; unfold redeems_any; simpl;
  [| destruct (nth_error _ _ ) as [[] | ]; auto].
  case_eq (nth_error outputs0 output_idx); intros; auto; destruct p as [s v].
  apply existsb_all_not; intros [input_idx [[tx' output_idx'] rl']] ?; simpl.
  unfold redeems_output_dec; simpl.
  unshelve eapply In_nth in H0; eauto;
  destruct H0 as [input_idx' []];
  unfold enumerate_list in *;
  rewrite combine_nth in H1; [| apply seq_length];
  inversion H1; clear H1; rewrite H3;
  rewrite seq_nth in H3; simpl in H3;
  rewrite combine_length in H0; apply Nat.min_glb_lt_iff in H0; intuition; subst;
  unshelve erewrite nth_error_nth; eauto;
  rewrite H4, H.

  rewrite !andb_false_iff; repeat left;
  pose proof (nth_error_nth _ _ input_idx (tx', rl', rl') H2);
  unfold Index, Time, Satoshi in H0, H4; rewrite H4 in H0; clear H4;
  apply nth_error_In in H0; clear - H0.

  apply not_true_iff_false; intro;
  apply TxStub_beq_eq in H.

  (* falsify the recursive equality with a height function *)
  set (height_TxStub := fix height_TxStub (txs : TxStub) : nat :=
  match txs with
  | tx_stub inputs _ _ => S (list_max (map (fun inp => height_TxStub (fst (fst inp))) inputs))
  | coinbase _ _ => O
  end).
  set (get_height := fun inp : _ * Index * Time => height_TxStub (fst (fst inp))).

  apply (f_equal height_TxStub) in H.
  apply (in_map get_height _ _) in H0.
  pose proof list_max_le (map get_height inputs0) _ H0.
  subst get_height.
  simpl in H1, H.
  intuition.
Qed.

(** Lemma: outputs of the last added transaction are always unspent *)
Lemma fresh_outputs_unspent : forall tx_hist' tx time output_idx,
  tx_history_consistent (tx_hist' ++ [(tx, time)]) ->
  output_spent (tx_hist' ++ [(tx, time)]) (stub tx, output_idx) = false.
Proof.
  intros. pose proof H as H_consistent. destruct H.
  - pose proof app_cons_not_nil tx_hist' [] (tx0, time); symmetry in TXH_EMPTY; contradiction.
  - apply app_inj_tail in TXH_APPEND; destruct TXH_APPEND as [H1 H2]; subst; inversion H2; subst; clear H2.
    rename tx1 into tx, time0 into time, tx_hist'0 into tx_hist'.

    simpl. unfold spent_output_dec. rewrite existsb_app. simpl.
    rewrite orb_false_iff. rewrite orb_false_r.
    rewrite TxStub_eq_beq. simpl.
    split; apply existsb_all_not; intros.
    {
      destruct x as [tx' time']; simpl in *.
      rewrite andb_false_iff; left.
      apply not_true_iff_false; intro.
      apply TxStub_beq_eq in H1.
      apply In_nth_error in H0.
      destruct H0 as [i]. symmetry in H0.
      assert (nth_error tx_hist' i <> None) as Hyp by congruence; apply nth_error_Some in Hyp.
      assert (i < Datatypes.length (tx_hist' ++ [(tx, time)])) by (rewrite app_length; omega).

      destruct (transaction_uniqueness _ H_consistent i (length tx_hist') tx' time' tx time); auto; [
      rewrite app_length; simpl; omega |
      rewrite nth_error_app1; auto |
      rewrite nth_error_app2; auto; rewrite minus_diag; auto | omega].
    }
    {
      apply in_app_or in H0.
      destruct H0.
      {
        destruct x as [tx' time']; simpl.
        unfold redeems_any. destruct (tx.out(_)) as [[]|]; auto.
        apply existsb_all_not. intros [input_idx [[tx_r tx_r_output_idx] rl]] ?; simpl.
        unfold redeems_output_dec;
        unshelve eapply In_nth in H1; eauto;
        destruct H1 as [input_idx' []];
        unfold enumerate_list in *;
        rewrite combine_nth in H2; [| apply seq_length];
        inversion H2; clear H2; rewrite H4;
        rewrite seq_nth in H4; simpl in H4;
        rewrite combine_length in H1; apply Nat.min_glb_lt_iff in H1; intuition; subst;
        unshelve erewrite nth_error_nth; eauto;
        rewrite H5.

        rewrite !andb_false_iff; repeat left.
        pose proof (nth_error_nth _ _ input_idx (tx_r, rl, rl) H3);
        unfold Index, Time, Satoshi in H1, H5; rewrite H5 in H1; clear H5.

        apply not_true_iff_false; intro H_eq.
        apply TxStub_beq_eq in H_eq. subst.

        apply In_nth_error in H0.
        destruct H0 as [i]. symmetry in H0.
        assert (nth_error tx_hist' i <> None) as Hyp by congruence; apply nth_error_Some in Hyp.
        assert (i < Datatypes.length (tx_hist' ++ [(tx, time)])) by (rewrite app_length; omega).
        assert (Some (tx', time') = nth_error (tx_hist' ++ [(tx, time)]) i) by (rewrite nth_error_app1; auto).

        destruct (exists_preceding_output _ _ H_consistent H4 _ _ H5 _ _ _ _ H1)
        as [j [H_prev [T_j [time_j [_ [_ [? [H_eq _]]]]]]]].

        destruct (transaction_uniqueness _ H_consistent j (length tx_hist') T_j time_j tx time); auto; [
        apply nth_error_Some; congruence |
        rewrite app_length; simpl; omega |
        rewrite nth_error_app2; auto; rewrite minus_diag; auto | omega].
      }
      {
        simpl in H0; destruct H0; intuition; subst; simpl;
        apply no_self_redeem.
      }
    }
Qed.

Lemma redeems_any_impl_spent_output_dec: forall tx idx0 t1 t2 tx_hist t
      (CONS: tx_history_consistent tx_hist) (RED: redeems_any (stub tx) idx0 t1 t t2 = true)
      (IN1: In (t,t2) tx_hist) (IN2: In (tx, t1) tx_hist) (NEQ: t <> tx),
      spent_output_dec tx_hist (stub tx) idx0 = true.
Proof.
  intros.
  apply existsb_exists.
  exists (tx0, t1); splits; simpls; auto.
  splitt.
  - apply TxStub_eq_beq.
  - apply existsb_exists.
    exists (t, t2); splits; auto.
Qed.

(** Lemma: coinbase transactions cannot spend anything *)
Lemma coinbase_no_spend1: forall tx_hist txs cb t idx n es
            (CONS: tx_history_consistent (tx_hist ++ [(cb, t)]))
            (CB: stub cb = coinbase n es)
            (SPENT: output_spent (tx_hist ++ [(cb, t)]) (txs, idx) = true),
            output_spent tx_hist (txs, idx) = true.
Proof.
  ins.
  pose proof (fresh_outputs_unspent tx_hist cb t idx CONS) as PRF.
  unfold output_spent, spent_output_dec.
  unfold output_spent, spent_output_dec in SPENT.
  apply existsb_exists in SPENT; des.
  apply in_app_or in H; des.
  * apply existsb_exists.
    exists x; splits; auto.
    apply andb_true_intro; split; auto.
    apply existsb_exists.
    apply existsb_exists in H1; des.
    apply in_app_or in H1; des.
    - exists x0; split; auto.
    - exfalso.
      red in H1; des; auto.
      destruct x0; subst; simpls.
      unfold redeems_any in H2.
      destruct (nth_error (outputs txs) idx).
      + destruct p.
        apply existsb_exists in H2; des.
        inversion H1; subst.
        rewrite CB in H2.
        simpls; auto.
      + inversion H2.
  * apply existsb_exists in H1; des.
    simpls; des; auto.
    destruct x; inversion H; clear H; subst.
    simpls.
    apply TxStub_beq_eq in H0; subst.
    destruct x0 as [tx tm].
    pose proof (redeems_any_impl_spent_output_dec t0 idx t1 tm
                (tx_hist ++ [(t0, t1)]) tx CONS H2 H1).
    rewrite H in PRF; inversion PRF.
    - apply in_or_app; right; simpl; auto.
    - simpls.
      intro; subst.
      rewrite no_self_redeem in H2; inversion H2.
Qed.

Lemma fold_sum_from: forall l v1 v2,
     fold_left
     (fun (acc : Satoshi) (output : TxStub * Index) =>
      let (tx1, output_idx) := output in
      acc + match nth_error (outputs tx1) output_idx with
            | Some (_, v) => v
            | None => 0
            end) l (v1+v2) =
     fold_left
     (fun (acc : Satoshi) (output : TxStub * Index) =>
      let (tx1, output_idx) := output in
      acc + match nth_error (outputs tx1) output_idx with
            | Some (_, v) => v
            | None => 0
            end) l v1 + v2.
Proof.
  induction l; ins.
  destruct a; ins.
  assert (QQ: v2 + match nth_error (outputs t) i with
                           | Some (_, v) => v
                           | None => 0
                           end = match nth_error (outputs t) i with
                           | Some (_, v) => v
                           | None => 0
                           end + v2).
    rewrite Nat.add_comm; ins.
  rewrite <- plus_assoc.
  rewrite QQ.
  rewrite plus_assoc.
  rewrite IHl; ins.
Qed.

Lemma fold_sum_0: forall l v,
  fold_left
     (fun (acc : Satoshi) (output : TxStub * Index) =>
      let (tx1, output_idx) := output in
      acc + match nth_error (outputs tx1) output_idx with
            | Some (_, v) => v
            | None => 0
            end) l v =
     fold_left
     (fun (acc : Satoshi) (output : TxStub * Index) =>
      let (tx1, output_idx) := output in
      acc + match nth_error (outputs tx1) output_idx with
            | Some (_, v) => v
            | None => 0
            end) l 0 + v.
Proof.
  ins; pose proof (fold_sum_from l 0 v); ins.
Qed.

Lemma cons_update_UTXO: forall tx_hist tx0 t (CONS: tx_history_consistent (tx_hist ++ [(tx0, t)])),
                               incl (map fst (inputs (stub tx0))) (UTXO tx_hist).
Proof.
  intros.
  inversion CONS; [apply app_eq_nil in TXH_EMPTY; intuition; discriminate|];
  apply app_inj_tail in TXH_APPEND; intuition; inversion H0; subst; clear H0.
  inversion TXH_UPDATE; des; subst.
  - rewrite H; unfold incl; simpl; intuition.
  - unfold incl; intros.
    clear - H3 H4.
    induction (inputs (stub tx1)) using rev_ind; simpl in *; intuition.
    rewrite map_app in *; simpl in *; apply in_app_or in H4; simpl in *.
    destruct H4.
    + apply IHl; clear IHl; auto; intros.
      destruct (H3 i). rewrite app_length; simpl; intuition.
      exists x0. intuition. rewrite nth_error_app1 in H2; auto.
    + clear IHl; destruct H; intuition; subst.
      destruct (H3 (length l)); clear H3. rewrite app_length; simpl; intuition.
      des. rewrite nth_error_app2, minus_diag in H; auto; simpl in *.
      inversion H; subst; clear - H0.
      unfold redeemed_output_unspent in H0.
      rewrite <- surjective_pairing in H0.
      assumption.
Qed.

Lemma spent_update_inv : forall (tx_hist : list (Tx * Time)) (tx : Tx) (time : Time),
  tx_history_consistent (tx_hist ++ [(tx, time)]) ->
  forall (output : TxStub * Index),
  In output (STXO (tx_hist ++ [(tx, time)])) ->
  In output (STXO tx_hist) \/ In output (fst (split (inputs (stub tx)))).
Proof.
  intros.
  inversion H; [apply app_eq_nil in TXH_EMPTY; intuition; discriminate|];
  apply app_inj_tail in TXH_APPEND; intuition; inversion H2; subst; clear H2.
  unfold STXO, spent_unspent_outputs in *.
  do 2 (edestruct partition_filter as [HH _]; rewrite <- !HH in *; clear HH).
  rewrite <- map_split in *.
  unfold output_spent, spent_output_dec in *.
  apply filter_In in H0. des.
  destruct output as [tx j].
  apply existsb_exists in H1.
  des.
  apply existsb_exists in H3.
  des.
  apply TxStub_beq_eq in H2.
  destruct x as [tx' time'], x0 as [tx_redeemer time_redeemer]; simpl in *.
  apply in_app_or in H1; apply in_app_or in H3; subst; simpl in *.
  destruct H1 as [|[|]]; try contradiction.
  2 : {
    inversion H1; subst; clear H1.
    exfalso.
    pose proof fresh_outputs_unspent _ _ _ j H; unfold output_spent, spent_output_dec in *.
    pose proof all_not_existsb _ _ _ H1 (tx', time'); clear H1; simpl in H2.
    rewrite andb_false_iff, TxStub_eq_beq in H2.
    destruct H2; try discriminate.
    apply in_app_iff; right; intuition.
    pose proof all_not_existsb _ _ _ H1 (tx_redeemer, time_redeemer); simpl in H2.
    rewrite H2 in H4. discriminate.
    apply in_app_iff. auto.
  }
  {
    apply in_flat_map in H0.
    destruct H0 as [tx'' []].
    apply in_map_iff in H2 as [? []].
    inversion H2; subst; clear H2.
    destruct H3 as [|[|]]; try contradiction; [left | right].
    {
      apply filter_In; intuition.
      apply in_flat_map.
      exists tx'. intuition.
      apply in_split_l in H1. auto.
      apply in_map_iff. exists j; intuition; rewrite <- !H7 in *; auto.
      rewrite H7.
      apply existsb_exists.
      exists (tx', time'); rewrite andb_true_iff; intuition; simpl.

      apply TxStub_eq_beq.
      apply existsb_exists.
      exists (tx_redeemer, time_redeemer); intuition.
    }
    {
      rewrite H7 in *.
      apply in_map_iff.
      inversion H2; subst; clear H2.
      unfold redeems_any in H4.
      case_eq (nth_error (outputs (stub tx')) j); intros; rewrite H2 in *; try discriminate.
      destruct p.
      apply existsb_exists in H4.
      destruct H4 as [[input_idx input] []].
      exists input.
      unfold enumerate_list in H3.
      apply in_combine_r in H3 as H_in. intuition.
      simpl in *.
      unfold redeems_output_dec in H4.
      apply In_nth_error in H3.
      destruct H3 as [input_idx'].
      case_eq (tx_redeemer.in(input_idx)); intros;
      rewrite H6 in *; try discriminate.
      apply (map_nth_error snd) in H3 as H_input.
      apply (map_nth_error fst) in H3.
      rewrite map_split, combine_split in H3; [| rewrite seq_length; auto].
      simpl in H3.
      assert (nth_error (seq 0 (Datatypes.length (inputs (stub tx_redeemer)))) input_idx' <> None) as H_len
      by (unfold Index in *; congruence);
      apply nth_error_Some in H_len;
      rewrite seq_length in H_len.
      apply nth_error_nth_r with (d := 0) in H3.
      assert (tx_redeemer.in(input_idx) <> None) by congruence.
      apply nth_error_Some in H8.
      rewrite seq_nth in H3; auto. simpl in *. subst.
      destruct p as [[tx''' j'''] rl].
      rewrite !andb_true_iff in H4. des.
      apply TxStub_beq_eq in H3.
      apply beq_nat_true in H11. subst.
      rewrite map_split_r, combine_split in H_input; [| rewrite seq_length; auto].
      simpl in *.
      rewrite H6 in H_input.
      inversion H_input.
      auto.
    }
  }
Qed.

(** Lemma which describes the exact change in UTXO value after a new transaction *)
Lemma utxo_value_append :
  forall tx_hist tx t, tx_history_consistent (tx_hist ++ [(tx, t)]) ->
  UTXO_value (tx_hist ++ [(tx, t)]) =
  UTXO_value tx_hist + sum_outputs (stub tx) - sum_inputs (stub tx) .
Proof.
  intros.
  unfold sum_inputs, sum_outputs; simpl.
  unfold UTXO_value at 1, UTXO, spent_unspent_outputs, all_outputs.
  rewrite flat_map_concat_map;
  rewrite split_app_fst; rewrite map_app; rewrite concat_app.
  rewrite partition_app_snd; simpl.
  rewrite <- flat_map_concat_map. rewrite app_nil_r.
  rewrite fold_left_app.
  rewrite fold_sum_0.
  pose proof (fresh_outputs_unspent (tx_hist) tx0 t) as PP.
  assert (WW: forall (A : Type) (l : list A) (f : A -> bool),
              filter (fun x : A => negb (f x)) l = snd (partition f l)).
  { ins; pose proof (partition_filter A l f); des; eauto. }
  erewrite fold_left_sum_map with (g:= fun a : TxStub * Index =>
                                    (let (tx1, output_idx) := a in match nth_error (outputs tx1) output_idx with
                                     | Some (_, v) => v
                                     | None => 0
                                     end)).
  * rewrite plus_comm.
    erewrite fold_left_sum_map with (g:=fun a : TxStub * Index =>
                                      (let (tx1, output_idx) := a in match nth_error (outputs tx1) output_idx with
                                      | Some (_, v) => v
                                      | None => 0
                                      end)).
    - rewrite <- !WW.
      assert (QQ: fold_left (fun (acc : Satoshi) (output : TxStub * Index) =>
                 let (tx1, output_idx) := output in acc + match nth_error (outputs tx1) output_idx with
                                                          | Some (_, v) => v
                                                          | None => 0
                                                          end)
                 (snd (partition (output_spent (tx_hist ++ [(tx0, t)]))
                    (map (fun j : nat => (stub tx0, j)) (seq 0 (Datatypes.length (outputs (stub tx0))))))) 0
              =
              fold_left (fun (v : nat) (out_i : Exp * nat) => snd out_i + v) (outputs (stub tx0)) 0).
      {
      (* all outputs of tx0 are unspent *)
      rewrite <- WW.
      assert (EE: (filter (fun x : TxStub * Index => negb (output_spent (tx_hist ++ [(tx0, t)]) x))
       (map (fun j : nat => (stub tx0, j)) (seq 0 (Datatypes.length (outputs (stub tx0)))))) =
       (map (fun j : nat => (stub tx0, j)) (seq 0 (Datatypes.length (outputs (stub tx0)))))).
       {
         eapply filter_all; ins.
         apply in_map_iff in H0; des.
         subst.
         rewrite PP; ins.
       }
       rewrite EE.
       clear -H.
       erewrite fold_left_sum_map with (
                                g := fun a: TxStub * Index => (let (tx1, output_idx) := a
                                in match nth_error (outputs tx1) output_idx with
                                     | Some (_, v) => v
                                     | None => 0
                                     end)).
      * symmetry.
        unfold Satoshi, Index, Time in *.
        erewrite fold_left_sum_map with (g:=snd); try (ins; omega).
        assert ((map snd (outputs (stub tx0))) = (map
        (fun a : TxStub * Index =>
        let (tx1, output_idx) := a in match nth_error (outputs tx1) output_idx with
                                    | Some (_, v) => v
                                    | None => 0
                                    end)
        (map (fun j : nat => (stub tx0, j)) (seq 0 (Datatypes.length (outputs (stub tx0))))))).
        {
          clear H.
          destruct tx0; ins.
          destruct stub0; ins.
          * rewrite map_map.
            induction outputs0 using rev_ind; ins.
            rewrite length_app_1 with (l':=outputs0)(a:=x); ins.
            rewrite seq_app.
            rewrite !map_app.
            simpl.
            assert(QW: [snd x] = [match nth_error (outputs0 ++ [x]) (Datatypes.length outputs0) with
                                  | Some (_, v) => v
                                  | None => 0
                                  end]).
            { f_equal.
              rewrite nth_error_app2; ins.
              rewrite Nat.sub_diag; simpl.
              destruct x; ins. }
            rewrite <- QW; clear QW.
            assert(QW: map snd outputs0 = map (fun x0 : nat => match nth_error (outputs0 ++ [x]) x0 with
                     | Some (_, v) => v
                     | None => 0
                     end) (seq 0 (Datatypes.length outputs0))).
                     { rewrite IHoutputs0. clear.
                        apply map_ext_in; intros.
                        simpl.
                        rewrite nth_error_app1. auto.
                        apply in_seq in H. intuition.
                     }
            rewrite QW; ins.
          * rewrite map_map.
            induction outputs0 using rev_ind; ins.
            rewrite length_app_1 with (l':=outputs0)(a:=x); ins.
            rewrite seq_app.
            rewrite !map_app.
            simpl.
            assert(QW: [snd x] = [match nth_error (outputs0 ++ [x]) (Datatypes.length outputs0) with
                                  | Some (_, v) => v
                                  | None => 0
                                  end]).
            { f_equal.
              rewrite nth_error_app2; ins.
              rewrite Nat.sub_diag; simpl.
              destruct x; ins. }
            rewrite <- QW; clear QW.
            assert(QW: map snd outputs0 = map (fun x0 : nat => match nth_error (outputs0 ++ [x]) x0 with
                     | Some (_, v) => v
                     | None => 0
                     end) (seq 0 (Datatypes.length outputs0))).
                     {
                      rewrite IHoutputs0. clear.
                      apply map_ext_in; intros.
                      simpl.
                      rewrite nth_error_app1. auto.
                      apply in_seq in H. intuition.
                     }
            rewrite QW; ins.
        }
        assert (forall l1 l2, l1 = l2 -> fold_left Init.Nat.add l1 0 = fold_left Init.Nat.add l2 0).
        { ins. subst. auto. }
        apply H1; ins.
      * destruct a; ins.
    }
  rewrite <- QQ; clear QQ.
  assert(MNS: forall a b c d, a = c /\ b = d -> a - b = c - d) by (ins; des; subst; reflexivity).
  rewrite <- !WW; clear WW.
  rewrite Nat.add_sub_swap.
  assert( QQQ:
  fold_left Init.Nat.add
  (map
     (fun a : TxStub * Index =>
      let (tx1, output_idx) := a in match nth_error (outputs tx1) output_idx with
                                    | Some (_, v) => v
                                    | None => 0
                                    end)
     (filter (fun x : TxStub * nat => negb (output_spent (tx_hist ++ [(tx0, t)]) x))
        (map (fun j : nat => (stub tx0, j)) (seq 0 (Datatypes.length (outputs (stub tx0))))))) 0 =
  fold_left
  (fun (acc : Satoshi) (output : TxStub * Index) =>
   let (tx1, output_idx) := output in
   acc + match nth_error (outputs tx1) output_idx with
         | Some (_, v) => v
         | None => 0
         end)
  (filter (fun x : TxStub * Index => negb (output_spent (tx_hist ++ [(tx0, t)]) x))
     (map (fun j : nat => (stub tx0, j)) (seq 0 (Datatypes.length (outputs (stub tx0)))))) 0).
  {
      symmetry. erewrite fold_left_sum_map; eauto.
      ins. destruct a; ins.
  }
  rewrite <- QQQ; clear QQQ.
  apply Nat.add_cancel_r.
  + unfold UTXO_value, UTXO, spent_unspent_outputs, all_outputs.
    erewrite !fold_left_sum_map with (g:=fun (a : TxStub * nat)=> let (tx1, output_idx) := a in match nth_error
          (outputs tx1) output_idx with
                                   | Some (_, v) => v
                                   | None => 0
                                   end); try destruct a; eauto using Nat.add_comm.
    rewrite !sum_fold_equiv.
    edestruct partition_filter.
    erewrite <- H1; clear H1 H0.
    rewrite filter_sum_true_total_minus_false2 with (p2:= fun x : TxStub * nat => negb (output_spent tx_hist x)).
    apply MNS; split; clear MNS; ins.
    ** erewrite fold_left_sum_map with (g:=get_input_value); try (ins; omega).
       rewrite <- sum_fold_equiv.
       assert(QQQ: Permutation
       (filter (fun a : TxStub * nat =>
                negb (output_spent tx_hist a) && negb (negb (output_spent (tx_hist ++ [(tx0, t)]) a)))
        (flat_map (fun tx1 : Tx => map (fun j : nat => (stub tx1, j)) (seq 0 (Datatypes.length (outputs (stub tx1)))))
           (fst (split tx_hist)))) (fst (split (inputs (stub tx0))))).
       {
          apply NoDup_Permutation.
          * apply nodup_filter.
            apply tx_hist_prefix_consistent with (tx_hist1:=tx_hist)(suff:=[(tx0, t)]) in H; ins.
            clear PP.
            induction tx_hist using rev_ind; ins; try apply NoDup_nil.
            rewrite split_app_fst.
            rewrite flat_map_concat_map.
            rewrite !map_app.
            rewrite concat_app.
            apply NoDup_iff; ins.
            - eapply tx_hist_prefix_consistent in H; eauto.
              rewrite <- flat_map_concat_map; eauto.
            - destruct x; simpl.
              rewrite app_nil_r.
              apply FinFun.Injective_map_NoDup.
              + red; ins; inversion H0; ins.
              + apply seq_NoDup.
            - destruct x; simpls; rewrite app_nil_r in H0.
              destruct x0.
              assert (EQ1: t2 = stub t0).
              {
                clear - H0. apply in_split_l in H0. simpl in *.
                rewrite <- map_split, map_map in H0.
                simpl in H0.
                apply in_map_iff in H0.
                destruct H0. intuition.
              }
              rewrite EQ1 in *.
              intro CONTRA.
              assert (CC1: In (stub t0) (map stub (fst (split tx_hist)))).
              {
                clear - CONTRA.
                apply in_split_l in CONTRA. simpl in *.
                rewrite <- map_split, concat_map, map_map, <- flat_map_concat_map in CONTRA.
                apply in_flat_map in CONTRA.
                destruct CONTRA as [t' [? ?]].
                rewrite map_map in H0. simpl in H0.
                rewrite in_map_iff in H0.
                destruct H0 as [? [? ?]].
                apply (in_map stub) in H. congruence.
              }
              (* nonunique transaction, on in [(t0, t1)], one in tx_hist *)
              pose proof (transaction_uniqueness_strong (tx_hist++[(t0, t1)]) H) as UNQ.
              clear - CC1 UNQ.
              apply In_nth_error in CC1.
              destruct CC1 as [i].
              specialize (UNQ i (length tx_hist) (stub t0) (stub t0)).
              assert (nth_error (map stub (fst (split tx_hist))) i <> None) by congruence;
              apply nth_error_Some in H0. pose proof H0 as H1. rewrite map_length, split_length_l in H0.
              rewrite UNQ in H0; try rewrite app_length; simpl; intuition.
              rewrite map_length, split_length_l, app_length; simpl; intuition.
              rewrite map_length, split_length_l, app_length; simpl; intuition.
              rewrite split_app_fst, map_app, nth_error_app1; auto.
              rewrite split_app_fst, map_app, nth_error_app2, map_length, split_length_l, minus_diag; auto.
              rewrite map_length, split_length_l; simpl; intuition.
          * destruct H. try (apply app_eq_nil in TXH_EMPTY; des; inversion H0).
            assert (tx1 = tx0 /\ t = time /\ tx_hist = tx_hist').
              apply app_inj_tail in TXH_APPEND. intuition; inversion H1; auto.
            des; subst.
            unfold is_consistent_update in TXH_UPDATE; des.
            - rewrite H0; simpl; apply NoDup_nil.
            - rewrite <- map_split; ins.
          * assert (QWE: forall a,
                         negb (output_spent tx_hist a) && negb (negb (output_spent (tx_hist ++ [(tx0, t)]) a)) = true
                         <->
                         In a (fst (split (inputs (stub tx0))))).
            {
              ins.
              split; ins.
              * (* unspent before update, spent after -> an input of the added tx *)
                clear - H H0.
                rewrite andb_true_iff, !negb_true_iff, negb_false_iff in H0; destruct H0.
                assert (In a (STXO (tx_hist ++ [(tx0, t)]))).
                {
                  unfold STXO, spent_unspent_outputs.
                  edestruct partition_filter as [? _]; rewrite <- H2; clear H2.
                  apply filter_In. intuition.
                  unfold all_outputs.
                  rewrite <- map_split, map_app.
                  simpl.
                  rewrite in_flat_map.
                  clear - H1.
                  unfold output_spent, spent_output_dec in H1.
                  destruct a as [tx_out j]; simpl in *.
                  apply existsb_exists in H1. des.
                  exists (fst x).
                  apply (in_map fst) in H; rewrite map_app in H; simpl in *; intuition.
                  apply TxStub_beq_eq in H0; subst; simpl in *.
                  apply in_prod_aux, in_seq; simpl; intuition.
                  clear - H1.
                  apply existsb_exists in H1. des.
                  unfold redeems_any in H0.
                  case_eq (nth_error (outputs (stub (fst x))) j); intros; rewrite H1 in *.
                  - assert (nth_error (outputs (stub (fst x))) j <> None) by congruence;
                    apply nth_error_Some; auto.
                  - discriminate.
                }
                assert (~ In a (STXO tx_hist)). {
                  intro. clear - H0 H3.
                  unfold STXO, spent_unspent_outputs in H3.
                  edestruct partition_filter as [? _]; rewrite <- H in H3; clear H.
                  apply filter_In in H3. intuition. congruence.
                }
                pose proof spent_update_inv _ _ _ H a H2.
                intuition.
              * rewrite andb_true_iff, !negb_true_iff, negb_false_iff; split.
                clear - H H0.
                inversion H; [apply app_eq_nil in TXH_EMPTY; intuition; discriminate|].
                apply app_inj_tail in TXH_APPEND; intuition; inversion H2; subst; clear H2.
                unfold is_consistent_update in *.
                des; subst.
                - rewrite H1 in H0; simpl in *; contradiction.
                - apply In_nth_error in H0. destruct H0 as [i].
                  assert (nth_error (fst (split (inputs (stub tx1)))) i <> None) by congruence.
                  apply nth_error_Some in H6. rewrite split_length_l in H6.
                  specialize (H5 i H6). des.
                  unfold redeemed_output_unspent, UTXO, spent_unspent_outputs in H7.
                  edestruct partition_filter as [_ ?].
                  rewrite <- H10 in H7; clear H10. apply filter_In in H7; des.
                  rewrite negb_true_iff in H10.
                  apply (map_nth_error fst) in H5.
                  rewrite map_split in H5.
                  rewrite H5 in H0. inversion H0. subst.
                  rewrite <- surjective_pairing in H10.
                  auto.
                - pose proof spent_update' _ _ _ _ H eq_refl.
                  apply H1 in H0. unfold STXO, spent_unspent_outputs in H0.
                  edestruct partition_filter as [H2 _]; rewrite <- H2 in H0; clear H2.
                  apply filter_In in H0.
                  intuition.
            }
            ins; split.
            - specialize (QWE x).
              destruct QWE as [Q1 Q2].
              ins; apply filter_In in H0; des.
              assert (negb (output_spent tx_hist x) && negb (negb (output_spent (tx_hist ++ [(tx0, t)]) x)) = true)
                by (apply andb_true_iff; split; ins); ins.
            - ins.
              remember H0 as INPS; clear HeqINPS.
              apply QWE in H0.
              apply filter_In; split; ins.
              (* this input exists in the previous list *)
              pose proof (exists_preceding_output).
              apply in_flat_map.
              apply In_nth_error in INPS.
              destruct INPS as [input_idx].
              destruct x as [T_j' output_idx'].
              destruct (fun HH1 HH2 => H1 _ (length tx_hist) H HH1 tx0 t HH2 T_j' output_idx'
              (nth input_idx (snd (split (inputs (stub tx0)))) 0) input_idx)
              as [j [? [T_j [time_j [s [v]]]]]].
              rewrite app_length; simpl; intuition.
              rewrite nth_error_app2, minus_diag; simpl; auto.
              clear - H2;
              set (ins := inputs (stub tx0)) in *;
              pose proof split_combine ins;
              pose proof split_length_l ins; pose proof split_length_r ins;
              destruct (split ins); simpl in *;
              assert (nth_error l input_idx <> None) by (unfold Index; congruence);
              apply nth_error_Some in H3;
              unfold Index, Time in *;
              rewrite (nth_error_nth _ _ _ (T_j', output_idx', 0)); intuition; rewrite <- H;
              rewrite combine_nth; intuition;
              rewrite (nth_error_nth _ _ _ (T_j', output_idx')) in H2; auto;
              congruence.
              des; exists T_j; intuition.
              {
                symmetry in H4. rewrite nth_error_app1 in H4; auto. apply nth_error_In in H4.
                apply (in_map fst) in H4. simpl in *. rewrite map_split in H4. auto.
              }
              {
                simpl in *. subst.
                apply in_prod_aux.
                apply in_seq. simpl.
                intuition. apply nth_error_Some. congruence.
              }
       }
       assert (CONV: map get_input_value (inputs (stub tx0)) = (map
       (fun a : TxStub * Index =>
        let (tx1, output_idx) := a in match nth_error (outputs tx1) output_idx with
                                    | Some (_, v) => v
                                    | None => 0
                                    end) (fst (split (inputs (stub tx0)))))).
       {
         clear QQQ.
         induction (inputs (stub tx0)); ins.
         destruct a, p, (split l); ins.
         rewrite IHl; ins; clear IHl.
         unfold get_output_value.
         case_eq (nth_error (outputs t1) i); simpl.
         * ins.
           eapply nth_error_nth_r with (d := (?[e], 0)) in H0.
           change 0 with (snd (?e, 0)). rewrite map_nth, H0.
           instantiate (e := fst p). destruct p. auto.
         * intros. apply nth_error_None in H0. rewrite nth_overflow; auto; rewrite map_length; auto.
       }
       unfold Index, Satoshi, Time in *.
       rewrite CONV; clear CONV.
       eapply Permutation_map with (f:=(fun a : TxStub * nat =>
       let (tx1, output_idx) := a in match nth_error (outputs tx1) output_idx with
                                    | Some (_, v) => v
                                    | None => 0
                                    end)) in QQQ.
       rewrite !sum_fold_equiv.
       apply sum_permutation_invariant; eauto.
       ** apply monotonic_contra; unfold output_spent, monotonic; intros; destruct a;
          eapply spent_output_monotonic; eauto.
      + unfold UTXO_value.
        erewrite fold_left_sum_map with (g:=get_input_value); intuition.
        assert (QQQ: fold_left (fun (acc : Satoshi) (output : TxStub * Index) =>
                           let (tx1, output_idx) := output in acc + match nth_error (outputs tx1) output_idx with
                                                                    | Some (_, v) => v
                                                                    | None => 0
                                                                    end) (UTXO tx_hist) 0 =
                     fold_left Init.Nat.add
                    (map
                       (fun output : TxStub * nat =>
                        let (tx1, output_idx) := output in match nth_error (outputs tx1) output_idx with
                                                           | Some (_, v) => v
                                                           | None => 0
                                                           end) (UTXO tx_hist)) 0).
        { erewrite fold_left_sum_map with (
            g:=fun output : TxStub * nat =>
                let (tx1, output_idx) := output in match nth_error (outputs tx1) output_idx with
                                                   | Some (_, v) => v
                                                   | None => 0
                                                   end); intuition. }
        rewrite QQQ; clear QQQ.
        unfold get_input_value.
        pose proof (cons_update_UTXO tx_hist tx0 t H) as UPD.
        assert (QQQ: (map (fun input : TxStub * Index * Time => let (p, _) := input in let (stb, idx0) := p
                      in get_output_value stb idx0) (inputs (stub tx0)))
                      = (map (fun output : TxStub * nat =>
                                  let (tx1, output_idx) := output in match nth_error (outputs tx1) output_idx with
                                         | Some (_, v) => v
                                         | None => 0
                                         end) (map fst (inputs (stub tx0))))).
        {
          rewrite map_map. apply map_ext_in; intros.
          destruct a as [[tx_in output_idx] rl]. simpl. unfold get_output_value.
          rewrite <- nth_default_eq. unfold nth_default.
          case_eq (nth_error (outputs tx_in) output_idx); intros.
          eapply map_nth_error in H1; rewrite H1; auto.
          eapply map_nth_error_None in H1.
          rewrite H1.
          auto.
        }
        unfold Satoshi, Index, Time in *.
        rewrite QQQ; clear QQQ.
        apply fold_sum_incl_map.
        {
          inversion H; [
          symmetry in TXH_EMPTY; apply app_cons_not_nil in TXH_EMPTY; contradiction |].
          apply app_inj_tail in TXH_APPEND; destruct TXH_APPEND; inversion H1; subst.
          clear - TXH_UPDATE. unfold is_consistent_update in *. des; subst.
          rewrite H; simpl; apply NoDup_nil.
          assumption.
        }
        auto.
    - destruct a; ins.
  * destruct a; ins.
Qed.

Lemma utxo_value_suffix :
  forall tx_hist suff, tx_history_consistent (tx_hist ++ suff) ->
  UTXO_value (tx_hist ++ suff) =
  fold_left (fun acc tx => acc + sum_outputs (stub tx) - sum_inputs (stub tx))
  (map fst suff) (UTXO_value tx_hist).
Proof.
  intros.
  induction suff as [| [[tx wit] time]] using rev_ind; simpl.
  - rewrite app_nil_r. auto.
  - rewrite !app_assoc in *.
    rewrite map_app, fold_left_app; simpl.
    pose proof H as H_consistent.
    destruct H; [pose proof app_cons_not_nil; exfalso; congruence |].
    apply app_inj_tail in TXH_APPEND; destruct TXH_APPEND as [H1 H2]; subst.
    rewrite utxo_value_append, IHsuff; auto.
Qed.

(** Theorem: in a consistent transaction history, the total UTXO value is bounded above by the sum of coinbase outputs *)
Theorem UTXO_value_bounded_by_coinbase_value :
  forall tx_hist, tx_history_consistent tx_hist -> UTXO_value tx_hist <= coinbase_value tx_hist.
Proof.
  intros tx_hist H_consistent.
  induction tx_hist as [ | [tx output_idx]] using rev_ind.
  - reflexivity.
  - pose proof H_consistent as H_consistent'. destruct H_consistent.
    + pose proof app_cons_not_nil tx_hist [] (tx, output_idx); symmetry in TXH_EMPTY; contradiction.
    + apply app_inj_tail in TXH_APPEND; destruct TXH_APPEND as [H1 H2]; subst; inversion H2; subst; clear H2.
      apply IHtx_hist in H_consistent as H_prefix; clear IHtx_hist.

      unfold coinbase_value;
      rewrite split_app_fst; rewrite map_app; simpl;
      rewrite fold_left_app; simpl; fold (coinbase_value tx_hist').

      destruct TXH_UPDATE as [[bh [outputs [H_coin _]]] | [H_value [_ [H_inputs _]]]].
      * destruct tx0; simpl in *; subst.
        rewrite utxo_value_append; auto; simpl; unfold sum_inputs; omega.
      * destruct tx0 as [[] ?]; try contradiction; simpl in *.
        rewrite utxo_value_append; auto; simpl;
        unfold nonincreasing_value in *; omega.
Qed.

(** Theorem: in a consistent transaction history, the sum of a transaction's inputs is bounded above
    by the the total UTXO value at the time of the transaction's addition *)
Theorem UTXO_dominate_inputs : forall (tx_hist : list (Tx * Time)) (tx : Tx) (time : Time),
  tx_history_consistent (tx_hist ++ [(tx, time)]) ->
  sum_inputs (stub tx) <= UTXO_value tx_hist.
Proof.
  intros.
  pose proof cons_update_UTXO _ _ _ H.
  unfold sum_inputs, UTXO_value.
  unfold Satoshi in *.
  set (g' := fun output : TxStub * Index =>
    let (tx1, output_idx) := output in
    match nth_error (outputs tx1) output_idx with
    | Some (_, v) => v
    | None => 0
    end);
  rewrite fold_left_sum_map with (g := get_input_value); [|intuition];
  rewrite fold_left_sum_map with (g := g'); intuition.

  unfold get_input_value;
  erewrite map_ext_in with (g := fun i => g' (fst i)).
  2 : {
    intros. destruct a as [[]]. simpl. unfold get_output_value.
    case_eq (nth_error (outputs t) i); intros.
    destruct p.
    rewrite nth_error_nth_r with (p := s); auto.
    apply (map_nth_error snd) in H2; auto.
    apply nth_error_None in H2.
    apply nth_overflow. rewrite map_length.
    auto.
  }
  rewrite <- map_map.
  unshelve eapply (fold_sum_incl_map _ (map fst (inputs (stub tx0))) (UTXO tx_hist) g' _ H0);
  clear - H.
  inversion H. pose proof app_cons_not_nil. congruence.
  apply app_inj_tail in TXH_APPEND. des.
  inversion H1.
  subst. clear - TXH_UPDATE.
  inversion TXH_UPDATE; des; subst.
  rewrite H. apply NoDup_nil.
  auto.
Qed.

(* Blockchain *)

(** A blockchain under the same Dolev-Yao approach as above.
    Transactions and witnesses are segregated, but stored as lists rather than merkle trees,
    and the witnesses aren't stored inside the coinbase transaction. *)
Inductive Blockchain : Set :=
  | Empty
  | Block (prevBlock : Blockchain)
          (transactions : list TxStub)
          (witnesses : list (list (list StackValue)))
          (timestamp : Time).

Fixpoint bc_to_tx_history (bc : Blockchain) : TxHistory :=
  match bc with
  | Empty => []
  | Block bc' txs witnesses time => bc_to_tx_history bc' ++ map (fun tx_w : TxStub * list (list StackValue) =>
    let (txstub, w) := tx_w in ({| stub := txstub; witnesses := w|}, time)) (combine txs witnesses)
  end.

Definition BlockHeight := nat.

Fixpoint block_height (bc : Blockchain) : BlockHeight :=
  match bc with
  | Empty => 0
  | Block bc' _ _ _ => S (block_height bc')
  end.

Definition transaction_fee (tx : TxStub) : Satoshi :=
  match tx with
  | coinbase _ _ => 0
  | tx_stub inputs outputs _ => sum_inputs tx - sum_outputs tx
  end.

Definition block_reward_function := BlockHeight -> Satoshi.

(* Could change Satoshi definition to N later to make real calculations possible *)
Definition BTC : N := 100 (* 100000000 *).
Definition halving_interval : N := 21 (* 210000 *).

Definition block_reward : block_reward_function :=
  fun bh =>
    let halvings := N.div (N.of_nat bh) halving_interval in
    N.to_nat (N.shiftr (50 * BTC) halvings).

(** There has to be exactly one coinbase transaction and it must be the first one *)
Definition only_first_tx_coinbase (transactions : list TxStub) : Set :=
  (* also automatically requires nonemptiness *)
  ({ bh & { outputs | nth_error transactions 0 = Some (coinbase bh outputs) }}) *
  forall i, 0 < i < length transactions -> exists inputs outputs abslock,
  nth_error transactions i = Some (tx_stub inputs outputs abslock).

Definition only_first_tx_coinbase_dec (transactions : list TxStub) :
  only_first_tx_coinbase transactions + (only_first_tx_coinbase transactions -> False).
Proof.
  induction transactions as [| stub] using rev_rect.
  - unfold only_first_tx_coinbase. right. intros [[bh [outputs H]] _].
    simpl in H. discriminate.
  - destruct IHtransactions as [IH | IH].
    {
      destruct stub as [inputs outputs abslock| bh outputs]; [left | right].
      {
        split.
        - destruct IH as [[bh [outputs']] _]. exists bh, outputs'.
          rewrite nth_error_app1; [ assumption | ].
          apply nth_error_Some. congruence.
        - intros. destruct IH as [_ IH]. specialize (IH i).
          rewrite app_length in H; simpl in H;
          assert (0 < i < length transactions \/ i = length transactions) by omega; clear H; destruct H0.
          + specialize (IH H). destruct IH as [inputs' [outputs' [abslock' IH]]].
            exists inputs', outputs', abslock'.
            rewrite nth_error_app1; intuition.
          + clear IH. exists inputs, outputs, abslock. subst.
            rewrite nth_error_app2; intuition. rewrite minus_diag; auto.
      }
      {
        destruct IH as [[bh' [outputs' H_nonempty]] _].
        intros [_ H]. specialize (H (length transactions)).
        destruct H as [inputs'' [outputs'' [abslock'' H]]].
        - rewrite app_length; simpl; split; [ apply nth_error_Some; congruence | omega ].
        - rewrite nth_error_app2 in H; auto. rewrite minus_diag in H. simpl in H. congruence.
      }
    }
    {
      destruct transactions; simpl.
      {
        clear IH. destruct stub as [inputs outputs abslock| bh outputs].
        - right; intros [[? [? H]] _]; simpl in H; congruence.
        - left.
          + split. exists bh, outputs. auto. simpl.
            intros. omega.
      }
      {
        right. intro. apply IH; clear IH. unfold only_first_tx_coinbase in *. split.
        - destruct H as [[bh [outputs H]] _]. exists bh, outputs.
          rewrite app_comm_cons in H;
          rewrite nth_error_app1 in H; [ assumption | simpl; intuition ].
        - intros. destruct H as [_ H]. specialize (H i).
          destruct H as [inputs [outputs [abslock H]]].
          rewrite app_comm_cons; rewrite app_length; omega.
          exists inputs, outputs, abslock.
          rewrite app_comm_cons in H;
          rewrite nth_error_app1 in H; [ assumption | intuition ].
      }
    }
Defined.

Definition transaction_fees (transactions : list TxStub) : Satoshi :=
  fold_left plus (map (fun tx => transaction_fee tx) (tl transactions)) 0.

(** Coinbase contains the correct block height and output value *)
Definition coinbase_has_block_height_and_reward
  (transactions : list TxStub) (blockHeight : BlockHeight) (reward : block_reward_function) : Prop :=
  exists outputs, let cb := coinbase blockHeight outputs in
  nth_error transactions 0 = Some cb /\
  sum_outputs cb = reward blockHeight + transaction_fees transactions.

Definition coinbase_has_block_height_and_reward_dec
  (transactions : list TxStub) (blockHeight : BlockHeight) (reward : block_reward_function) :
  only_first_tx_coinbase transactions ->
  {coinbase_has_block_height_and_reward transactions blockHeight reward} +
  {~ coinbase_has_block_height_and_reward transactions blockHeight reward}.
Proof.
  intros [[bh [outputs H]] _].
  set (cb := coinbase bh outputs) in *.
  destruct (Nat.eq_dec bh blockHeight) as [H_eq_bh | H_neq_bh],
  (Nat.eq_dec (sum_outputs cb) (reward blockHeight + transaction_fees transactions)) as [H_eq_br | H_neq_br];
  subst cb; subst; [left; exists outputs; auto | | |]; right; intros [? []]; congruence.
Defined.

(** We already know that every prefix of a consistent tx history is consistent (tx_hist_prefix_consistent),
    so it is sufficient to require that the whole updated tx history is consistent and partial updates
    with a only a prefix of the block's transactions are guaranteed to be consistent. The only way to prove
    that the tx history updated with the whole block's transactions is consistent is to prove
    that updates by each of those transactions in order are consistent, essentially what Bitcoin is checking. *)
Definition transaction_updates_consistent (blockchain : Blockchain) : Prop :=
  tx_history_consistent (bc_to_tx_history blockchain).

Definition blockchain_update_consistent
  (prevBlockchain : Blockchain) (transactions : list TxStub) (witnesses : list (list (list StackValue))) (timestamp : Time) : Type :=
  (only_first_tx_coinbase transactions) *
  (coinbase_has_block_height_and_reward transactions (block_height prevBlockchain) block_reward /\
  transaction_updates_consistent (Block prevBlockchain transactions witnesses timestamp)).

Inductive blockchain_consistent (blockchain : Blockchain) : Prop :=
  | bc_empty (H_empty : blockchain = Empty)
  | bc_block prevBlockchain transactions witnesses timestamp
    (H_block : blockchain = Block prevBlockchain transactions witnesses timestamp)
    (H_witnesses : length transactions = length witnesses)
    (H_prev_consistent : blockchain_consistent prevBlockchain)
    (H_consistent_update : blockchain_update_consistent prevBlockchain transactions witnesses timestamp).

Lemma block_height_eq_coinbase_height : forall bc, blockchain_consistent bc ->
  block_height bc = coinbase_height (bc_to_tx_history bc).
Proof.
  intros.
  induction H; subst; simpl; auto.
  rewrite IHblockchain_consistent; clear IHblockchain_consistent.
  destruct H_consistent_update as [[[bh [outputs H_first_coinbase]] H_rest_tx] _].
  destruct transactions as [| cb rest]; try discriminate. (*  simpl. *)
  destruct witnesses0 as [| nil]; [discriminate|].
  inversion H_witnesses; clear H_witnesses; rename H1 into H_witnesses.
  unfold coinbase_height.
  rewrite split_app_fst. rewrite map_app.
  fold (coinbase_height (bc_to_tx_history prevBlockchain)).
  inversion H_first_coinbase; subst; clear H_first_coinbase.
  simpl in *.
  generalize dependent witnesses0.
  generalize dependent rest.
  induction rest using rev_ind; simpl in *;
  induction witnesses0 using rev_ind; simpl in *; intros;
  try now rewrite app_length in H_witnesses; simpl in H_witnesses; exfalso; intuition.
  - rewrite fold_left_app. simpl. reflexivity.
  - rewrite IHrest with (witnesses0 := witnesses0); clear IHrest;
    rewrite !app_length, Nat.add_cancel_r in H_witnesses; auto.
    2 : {
      intros.
      rewrite app_length in H_rest_tx; simpl in H_rest_tx; rewrite Nat.add_1_r in H_rest_tx.
      assert (0 < i < S (S (Datatypes.length rest))) by omega.
      specialize (H_rest_tx i H1). clear H1.
      destruct H_rest_tx as [inputs' [outputs' [abslock' H_tx]]].
      do 3 (unshelve eexists; eauto).
      rewrite app_comm_cons in H_tx; rewrite nth_error_app1 in H_tx; simpl; intuition.
    }
    {
      rewrite app_length in H_rest_tx; simpl in H_rest_tx; rewrite Nat.add_1_r in H_rest_tx.
      specialize (H_rest_tx (S (Datatypes.length rest))).
      destruct H_rest_tx as [inputs' [outputs' [abslock' H_tx]]]; [omega |].
      rewrite app_comm_cons in H_tx; rewrite nth_error_app2 in H_tx; simpl in *; [| omega].
      rewrite minus_diag in H_tx; simpl in H_tx; inversion H_tx.

      rewrite combine_distrib; auto.
      rewrite map_app.
      rewrite split_app. simpl.
      rewrite (surjective_pairing (split (map _ _))) at 1.
      simpl.
      rewrite map_app. simpl. rewrite app_comm_cons.
      rewrite !fold_left_app. simpl. auto.
    }
Qed.

(* Trivial, since we assume that in transaction_updates_consistent *)
Theorem bc_consistent_implies_tx_hist_consistent :
  forall bc, blockchain_consistent bc -> tx_history_consistent (bc_to_tx_history bc).
Proof.
  intros.
  destruct H; subst; simpl; auto.
  unfold blockchain_update_consistent in *.
  destruct H_consistent_update as [_ [_ ?]].
  unfold transaction_updates_consistent in H0.
  simpl in *.
  assumption.
Qed.

Corollary bc_consistent_implies_no_double_spending :
  forall bc, blockchain_consistent bc ->
  let tx_hist := bc_to_tx_history bc in

  forall i j T_i time_i T_j time_j, i < length tx_hist -> j < length tx_hist ->
  Some (T_i, time_i) = nth_error tx_hist i ->
  Some (T_j, time_j) = nth_error tx_hist j ->

    forall input_of_ith input_of_jth input_of_ith_index input_of_jth_index,
    nth_error (inputs (stub T_i)) input_of_ith_index = Some input_of_ith ->
    nth_error (inputs (stub T_j)) input_of_jth_index = Some input_of_jth ->
    (i, input_of_ith_index) <> (j, input_of_jth_index) ->
    fst input_of_ith <> fst input_of_jth.
Proof.
  intros ? ? ?. apply no_double_spending. apply bc_consistent_implies_tx_hist_consistent. auto.
Qed.

Corollary bc_consistent_implies_transaction_uniqueness :
  forall bc, blockchain_consistent bc ->
  let tx_hist := bc_to_tx_history bc in

  forall i j T_i time_i T_j time_j, i < length tx_hist -> j < length tx_hist ->
    Some (T_i, time_i) = nth_error tx_hist i ->
    Some (T_j, time_j) = nth_error tx_hist j ->
    stub T_i = stub T_j -> i = j.
Proof.
  intros ? ? ?. apply transaction_uniqueness. apply bc_consistent_implies_tx_hist_consistent. auto.
Qed.

(** Lemma: all non-coinbase transactions have the sum of their inputs bounded by the sum of their outputs
    (trivial, by definition of consistency) *)
Lemma all_updates_conservative : forall tx_hist tx time ins outs abslock,
  tx_history_consistent tx_hist ->
  In (tx, time) tx_hist ->
  stub tx = tx_stub ins outs abslock ->
  sum_outputs (stub tx) <= sum_inputs (stub tx).
Proof.
  intros.
  apply In_nth_error in H0.
  destruct H0 as [i].
  pose proof tx_hist_prefix_consistent_index _ i H.
  unfold tx_hist_prefix_to in *.
  assert (nth_error tx_hist i <> None) by congruence.
  apply nth_error_Some in H3.

  rewrite <- (nth_error_firstn i (tx_hist) H3) in H0.
  inversion H2.
  { simpl in *. rewrite TXH_EMPTY in *. apply nth_error_In in H0. inversion H0. }
  assert ((i + 1) <= length (tx_hist)) as Hi1 by omega.
  epose proof (firstn_length_le (tx_hist) Hi1).
  assert (length (firstn (i + 1) (tx_hist)) = (length tx_hist') + 1) as H_len_plus_1 by (eapply length_app_1; eauto).
  assert (i = length tx_hist') as Hi by omega. clear H_len_plus_1.
  remember (firstn (i + 1) (tx_hist)) as prefix_i.
  pose proof (list_last prefix_i tx_hist' i (tx0, time) (tx1, time0) Hi (eq_sym H0) TXH_APPEND) as H_eq.
  inversion H_eq; subst tx1 time; clear H_eq.

  inversion TXH_UPDATE; des.
  congruence.
  unfold nonincreasing_value in *.
  auto.
Qed.

Opaque block_reward.

(** Theorem: in a consistent blockchain, the total UTXO value is exactly the sum of block rewards *)
Theorem bc_consistent_utxo_value :
  forall bc, blockchain_consistent bc ->
  let tx_hist := bc_to_tx_history bc in
  UTXO_value tx_hist = fold_left plus (map block_reward (seq 0 (block_height bc))) 0.
Proof.
  induction bc; auto; intros.
  apply bc_consistent_implies_tx_hist_consistent in H as H_cons; simpl in H_cons.
  simpl in tx_hist.
  inversion H; [congruence|]; clear H.
  inversion H_block; subst; clear H_block.
  specialize (IHbc H_prev_consistent).
  simpl in IHbc. subst tx_hist.
  simpl (block_height _).
  rewrite <- Nat.add_1_r.
  rewrite seq_app. simpl (seq _ _).
  rewrite map_app. simpl (map _ _).
  rewrite fold_left_app. simpl.
  unfold Satoshi, BlockHeight in *.
  rewrite <- IHbc; clear IHbc.
  destruct H_consistent_update as [H_first [? H_tx_upd]].
  destruct H as [outputs []].
  destruct transactions0; [discriminate |].
  unfold only_first_tx_coinbase in H_first. simpl in H_first.
  inversion_clear H_first.
  destruct H1 as [bh [outputs' Heq]]; inversion Heq; subst; clear Heq.
  simpl in H; inversion H; subst; clear H.
  destruct witnesses1 as [| nil]; [discriminate|].
  simpl.

  set (cb := coinbase (block_height prevBlockchain) outputs) in *.
  assert (transaction_fees (cb :: transactions0) =
  fold_left plus (map (fun tx => sum_inputs (tx) - sum_outputs (tx)) transactions0) 0).
  {
    clear - H2.
    subst cb. unfold transaction_fees, transaction_fee in *. simpl in *.
    f_equal.
    induction transactions0 using rev_ind; auto.
    rewrite !map_app. simpl. rewrite IHtransactions0.
    destruct (H2 (Datatypes.length (transactions0 ++ [x])))
    as [inputs' [outputs' [al' H_tx]]];
    [rewrite !app_length; simpl; omega |].
    rewrite app_length, app_comm_cons, nth_error_app2,
    Nat.add_1_r, minus_diag in H_tx; simpl in H_tx; inversion_clear H_tx.
    auto.
    simpl; omega.

    clear - H2. intros. rewrite app_length, Nat.add_1_r in H2.
    destruct (H2 i) as [inputs' [outputs' [al' H_tx]]]; [omega |].
    exists inputs', outputs', al'.
    rewrite app_comm_cons, nth_error_app1 in H_tx; simpl in *; intuition.
  }
  rewrite H in H0; clear H.
  apply utxo_value_suffix in H_cons; simpl in H_cons; rewrite H_cons. clear H_cons.
  rewrite H0; clear H0.
  unfold sum_inputs at 3. simpl. rewrite !Nat.sub_0_r.

  rewrite plus_assoc.
  set (z := (UTXO_value _ + _)).
  rewrite map_map.
  rewrite map_ext with (g := fun x : TxStub * list (list StackValue) =>
    let (txstub, w) := x in {| stub := txstub; witnesses := w |}).
  2 : {
    intros.
    destruct a. auto.
  }

  clear - H_tx_upd H2 H_witnesses.
  unfold transaction_updates_consistent in *; simpl in *.
  assert (forall tx, In tx transactions0 -> sum_inputs tx >= sum_outputs tx).
  {
    intros.
    apply In_nth_error in H as H_i.
    destruct H_i as [i].
    assert (nth_error transactions0 i <> None) by congruence.
    apply nth_error_Some in H1.
    specialize (H2 (S i)).
    destruct H2. intuition.
    des. simpl in *.
    set (Tx_hist := (combine transactions0 witnesses1)) in *.
    set (w := nth i witnesses1 []).
    apply (all_updates_conservative (bc_to_tx_history prevBlockchain ++
      ({| stub := cb; witnesses := nil |}, timestamp0) ::
      map (fun tx_w : TxStub * list (list StackValue) =>
            let (txstub, w) := tx_w in ({| stub := txstub; witnesses := w |}, timestamp0))
      Tx_hist)
      (tx tx0 w) timestamp0 x x0 x1); simpl; auto; try congruence.
    apply in_app_iff. simpl. do 2 right.
    apply in_map_iff.
    exists (tx0, w). intuition.
    subst Tx_hist.
    apply (nth_error_In _ i).
    rewrite H0 in H2.
    inversion H2.
    rewrite nth_error_nth with (d := (tx0, [])).
    rewrite combine_nth.
    apply nth_error_nth_r with (d := tx0) in H0 .
    subst; subst w.
    rewrite H0. auto.
    auto.
    rewrite combine_length. inversion H_witnesses.
    rewrite Nat.min_id. auto.
  }

  destruct H_tx_upd;
  [pose proof app_cons_not_nil; exfalso; congruence |].
  clear - H H_witnesses;
  inversion H_witnesses; clear H_witnesses; rename H1 into H_witnesses.

  generalize dependent z.
  generalize dependent witnesses1.
  induction transactions0 using rev_ind; intros; simpl; auto.
  induction witnesses1 using rev_ind; intros; simpl; auto.
  rewrite !app_length in H_witnesses; simpl in H_witnesses; intuition.
  rewrite !app_length in H_witnesses; simpl in H_witnesses; clear IHwitnesses1.
  rewrite map_app, !fold_left_app. simpl.
  rewrite !plus_assoc. set (f := fold_left plus _ _) in *.

  rewrite combine_distrib in *; simpl in *; intuition.
  rewrite map_app; simpl in *.
  rewrite fold_left_app. simpl.
  rewrite Nat.add_cancel_r in H_witnesses.

  unshelve erewrite <- (IHtransactions0 _ witnesses1); eauto.
  intros; apply H; intuition.
  set (w := (z+f)).
  set (a := sum_inputs x).
  set (b := sum_outputs x).
  assert (a >= b).
  {
    subst a b.
    apply H.
    intuition.
  }

  unfold Satoshi.
  generalize dependent w.
  generalize dependent a.
  generalize dependent b.
  clear - H H_witnesses.
  intros.
  generalize dependent witnesses1.
  induction transactions0 using rev_ind; intros; simpl; try omega.
  induction witnesses1 using rev_ind; simpl; auto.
  rewrite !app_length in H_witnesses; simpl in H_witnesses; intuition.
  rewrite !app_length in H_witnesses; simpl in H_witnesses; clear IHwitnesses1.
  rewrite combine_distrib in *; simpl in *; intuition.
  rewrite map_app; simpl in *.

  rewrite !fold_left_app; simpl.
  rewrite <- IHtransactions0; intuition.
  set (c := sum_inputs x0).
  set (d := sum_outputs x0).
  assert (c >= d).
  {
    subst c d.
    apply H.
    intuition.
  }
  2 : {
    apply H.
    apply in_app_or in H1.
    apply in_or_app.
    intuition.
  }
  subst c d.
  omega.
Qed.
