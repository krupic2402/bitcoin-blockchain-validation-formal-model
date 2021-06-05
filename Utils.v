(* Checked with Coq version 8.10.2 *)
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.


Ltac simpls := simpl in *.
Ltac splits := repeat split.
Ltac des :=
  try match goal with
  | [ H: _ /\ _ |- _ ] => destruct H; des
  | [ H: _ \/ _ |- _ ] => destruct H; des
  | [ H: exists _, _ |- _ ] => destruct H; des
  | [ H: _ && _ = true |- _ ] => apply andb_prop in H; des
  | [ H: _ || _ = true |- _ ] => apply orb_prop in H; des
  end.

Ltac desb :=
  try match goal with
  | [ H: existsb _ _ = true |- _ ] => apply existsb_exists in H; des
  end.
Ltac ins := intros; simpl; eauto.
Ltac splitt :=
  splits; try match goal with
  | [ H:_ |- _ && _ = true ] => apply andb_true_intro; splits
  end.

Open Scope string_scope.
Open Scope list_scope.

Import ListNotations.

Lemma option_map_some: forall (A B : Type) (f : A -> B) (o : option A) (b : B),
  option_map f o = Some b -> exists (a : A), o = Some a.
Proof.
  intros; unfold option_map in H.
  destruct o; try congruence.
  exists a; trivial.
Qed.

Lemma NoDup_distinct: forall (A : Type) (l : list A) (i j : nat) (x y : A),
  NoDup l -> nth_error l i = Some x -> nth_error l j = Some y -> i <> j -> x <> y.
Proof.
  intros.
  intro H_v_eq.
  apply H2.
  assert (i < length l) by (apply nth_error_Some; congruence).
  apply (f_equal Some) in H_v_eq.
  rewrite <- H0, <- H1 in H_v_eq.
  eapply (NoDup_nth_error l) in H; eauto.
Qed.

Lemma incl_map: forall (A B : Type) (f : A -> B) (l1 l2 : list A),
  incl l1 l2 -> incl (map f l1) (map f l2).
Proof.
  unfold incl in *; intros.
  apply in_map_iff in H0; destruct H0; destruct H0.
  apply H in H1; apply in_map_iff; eauto.
Qed.

(** Trim list to singleton list containing only the nth element. *)
Definition keep_nth {A : Type} (l : list A) (n : nat) := firstn 1 (skipn (n-1) l).
(** Fill list with a specified default value up to but not including the nth element. *)
Definition default_up_to_nth {A : Type} (default : A) (l : list A) (n : nat) :=
  repeat default (n-1) ++ [nth n l default].

(** Attempt to convert the entire list using the fallible conversion function and
    return the converted list if all conversions succeeded. *)
Fixpoint coerce_list {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | a :: l' =>
    match f a with
    | Some b => option_map (fun l => b :: l) (coerce_list f l')
    | _ => None
    end
  end.

Definition enumerate_list {A: Type} (l : list A) :=
           combine (seq 0 (length l)) l.

Definition prod_map {A B A' B' : Type} (f : A -> A') (g : B -> B') (p : A * B) :=
  match p with
  | (a, b) => (f a, g b)
  end.

Lemma partition_map_in: forall (A B : Type) (f : A -> bool) (g : A -> B) (l l1 l2 : list A),
  partition f l = (l1, l2) -> forall a, In (g a) (map g l) -> In (g a) (map g l1) \/ In (g a) (map g l2).
Proof.
  intros.
  pose proof (@elements_in_partition _ f l l1 l2 H).
  apply in_map_iff in H0.
  do 2 destruct H0. rewrite <- H0.
  specialize (H1 x). destruct H1. clear H3. apply H1 in H2.
  destruct H2.
  + left. apply in_map. auto.
  + right. apply in_map. auto.
Qed.


Lemma list_last: forall {A : Type} (l l' : list A) i a a',
  i = length l' -> Some a = nth_error l i -> l = l' ++ [a'] -> a = a'.
Proof.
  intros A l l' i a a' H_index H_nth_error H_append.
  rename H_nth_error into H_tx_last_Ti.
  rewrite H_index in H_tx_last_Ti. rewrite H_append in H_tx_last_Ti.
  rewrite nth_error_app2 in H_tx_last_Ti; auto. rewrite <- minus_n_n in H_tx_last_Ti. simpl in H_tx_last_Ti.
  inversion H_tx_last_Ti. auto.
Qed.

Lemma length_app_1: forall (A : Type) (l l' : list A) a, l = l' ++ [a] -> length l = length l' + 1.
Proof.
  intros A l l' a H_append.
  rewrite H_append. rewrite app_length. auto.
Qed.


Lemma nth_error_firstn: forall {A : Type} j l, j < length l -> @nth_error A (firstn (j+1) l) j = @nth_error A l j.
Proof.
  intros.
  rewrite <- (firstn_skipn (j + 1) l) at 2.
  rewrite nth_error_app1; auto.
  rewrite firstn_length_le; try lia.
Qed.

Lemma partition_filter: forall A (l : list A) f,
filter f l = fst (partition f l) /\ filter (fun x => negb (f x)) l = snd (partition f l).
Proof.
  intros; split;
  induction l; auto; simpl; destruct (f a); rewrite IHl; case_eq (partition f l); intuition.
Qed.

Theorem partition_xor (A : Type) (f : A -> bool) (l l1 l2 : list A):
    partition f l = (l1, l2) ->
    forall x, In x l -> In x l1 -> In x l2 -> False.
Proof.
  intros.
  pose proof (@partition_filter A l f).
  destruct H3 as [HH1 HH2].
  rewrite H in HH1.
  rewrite H in HH2.
  simpl in *.
  rewrite <- HH1 in H1; clear HH1 H0.
  rewrite <- HH2 in H2; clear HH2.
  apply filter_In in H1.
  apply filter_In in H2.
  destruct H1 as [HH1 HH2].
  destruct H2 as [HH3 HH4].
  clear -HH4 HH2.
  rewrite HH2 in HH4; simpl in HH4; inversion HH4.
Qed.

Lemma split_app: forall (A B : Type) (l1 l2 : list (A * B)),
  split (l1 ++ l2) = (fst (split l1) ++ fst (split l2), snd (split l1) ++ snd (split l2)).
Proof.
  intros.
  induction l1 as [| [a b]]; simpl.
  - apply injective_projections; auto.
  - rewrite IHl1; rewrite (surjective_pairing (split l1)); auto.
Qed.

Lemma split_app_fst: forall (A B : Type) (l1 l2 : list (A * B)),
  fst (split (l1 ++ l2)) = fst (split l1) ++ fst (split l2).
Proof.
  intros.
  induction l1; intuition. simpl.
  case_eq (split (l1 ++ l2)). intros. simpl.
  rewrite H in IHl1. simpl in IHl1. subst.
  destruct (split l1). simpl. reflexivity.
Qed.

Lemma filter_app: forall (A : Type) (f : A -> bool) (l1 l2 : list A),
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
  intros.
  induction l1; intuition.
  simpl. destruct (f a); intuition.
  rewrite <- app_comm_cons. rewrite IHl1. auto.
Qed.

Lemma partition_app_fst: forall (A : Type) (f : A -> bool) (l1 l2 : list A),
  fst (partition f (l1 ++ l2)) = fst (partition f l1) ++ fst (partition f l2).
Proof.
  intros.
  pose proof (partition_filter A).
  destruct (H (l1 ++ l2) f) as [H1 _].
  destruct (H l1 f) as [H2 _].
  destruct (H l2 f) as [H3 _].
  rewrite <- H1, <- H2, <- H3 in *. clear H1 H2 H3 H.
  apply filter_app.
Qed.

Lemma partition_app_snd: forall (A : Type) (f : A -> bool) (l1 l2 : list A),
  snd (partition f (l1 ++ l2)) = snd (partition f l1) ++ snd (partition f l2).
Proof.
  intros.
  pose proof (partition_filter A).
  destruct (H (l1 ++ l2) f) as [_ H1].
  destruct (H l1 f) as [_ H2].
  destruct (H l2 f) as [_ H3].
  rewrite <- H1, <- H2, <- H3 in *. clear H1 H2 H3 H.
  apply filter_app.
Qed.

Definition monotonic {A : Type} (f1 f2 : A -> bool) :=
  forall a, f1 a = true -> f2 a = true.

Lemma partition_monotonic: forall (A : Type) (f1 f2 : A -> bool) (l : list A),
  monotonic f1 f2 -> incl (fst (partition f1 l)) (fst (partition f2 l)).
Proof.
  intros A f1 f2 l H_mono a H_in.
  destruct (partition_filter A l f1) as [H_filter _]. rewrite <- H_filter in H_in.
  apply filter_In in H_in. destruct H_in as [H_in H_true].
  apply H_mono in H_true.
  assert (In a l /\ f2 a = true) by auto.
  apply filter_In in H.
  destruct (partition_filter A l f2) as [H_true2 _].
  rewrite H_true2 in *.
  exact H.
Qed.

Lemma list_app_eq: forall A (l1 l2 : list A) a b, l1 ++ [a] = l2 ++ [b] <-> l1 = l2 /\ a = b.
Proof.
  intros; split.
  - intro H; assert (QQ: l1 = l2).
    {
      apply f_equal with (f:=@removelast A) in H.
      do 2 rewrite removelast_app in H; try (intuition; inversion H0).
      simpl in H; do 2 rewrite app_nil_r in H; assumption.
    }
    subst; intuition; apply app_inv_head in H;
    inversion H; auto.
  - intuition; subst; auto.
Qed.

Lemma map_split: forall A B (l : list (A*B)), map fst l = fst (split l).
Proof.
  intros.
  induction l using rev_ind; intuition.
  rewrite split_app_fst.
  rewrite map_app.
  rewrite IHl.
  reflexivity.
Qed.

Lemma nth_error_nth_r: forall A (l : list A) idx p, nth_error l idx = Some p -> forall d, nth idx l d = p.
Proof.
  induction l.
    * intros; apply nth_error_In in H; inversion H.
    * intros; destruct idx.
        simpl in *; inversion H; auto.
        simpl in *; apply IHl; auto.
Qed.

Lemma nth_error_nth: forall A (l : list A) idx d (LEN: idx < length l), nth_error l idx = Some (nth idx l d).
Proof.
  induction l.
    * intros; simpl in LEN; inversion LEN.
    * intros; destruct idx.
      - simpl in *; trivial.
      - simpl in *; apply IHl; lia.
Qed.

Lemma enumerate_list_nth: forall A idx (l : list A) p,
        nth_error l idx = Some p <-> nth_error (enumerate_list l) idx = Some (idx, p).
Proof.
  intros; split; intros.
  - unfold enumerate_list.
    assert (WW: length (seq 0 (Datatypes.length l)) = length l).
    { rewrite seq_length; trivial. }
    pose proof (combine_nth (seq 0 (Datatypes.length l)) l idx 0 p WW) as COMBINE.
    assert (idx = nth idx (seq 0 (Datatypes.length l)) 0).
    {
      rewrite seq_nth. lia.
      apply nth_error_Some. congruence.
    }
    rewrite <- H0 in COMBINE; clear H0.
    assert (p = nth idx l p).
    {
      symmetry. apply nth_error_nth_r.
      auto.
    }
    rewrite <- H0 in COMBINE; clear H0.
    assert (forall d, nth idx (combine (seq 0 (Datatypes.length l)) l) d = (idx, p)).
    {
      intros.
      rewrite nth_indep with (d':= (0,p)); auto.
      rewrite combine_length.
      rewrite seq_length.
      rewrite Nat.min_id.
      apply nth_error_Some.
      congruence.
    }
    rewrite nth_error_nth with (d:=(0,p)).
    rewrite COMBINE. trivial.
    rewrite combine_length.
    rewrite seq_length.
    rewrite Nat.min_id.
    apply nth_error_Some.
    congruence.
  - unfold enumerate_list in H.
    assert (WW: length (seq 0 (Datatypes.length l)) = length l).
    { rewrite seq_length; trivial. }
    assert (WWW: length (combine (seq 0 (Datatypes.length l)) l) = length l).
    { rewrite combine_length; rewrite seq_length; rewrite Nat.min_id; trivial. }
    assert (AA: idx < length (combine (seq 0 (Datatypes.length l)) l)).
    { apply nth_error_Some; intro; congruence. }
    rewrite WWW in AA.
    rewrite nth_error_nth with (d:=p).
    apply f_equal.

    pose proof (combine_nth (seq 0 (Datatypes.length l)) l idx 0 p WW) as COMBINE.

    rewrite nth_error_nth with (d:=(0,p)) in H.
    inversion H.
    rewrite COMBINE in H1.
    assert (snd (nth idx (seq 0 (Datatypes.length l)) 0, nth idx l p) = snd (idx, p))
      by (rewrite H1; trivial).
    simpl in H0; auto.
    rewrite WWW; auto.
    auto.
Qed.

Lemma firstn_app_one : forall A (l l' : list A) a i, i < Datatypes.length l ->
  firstn (i + 1) l = l' ++ [a] -> firstn i l = l'.
Proof.
  intros ? ? ? ? ? H_length H;
  apply f_equal with (f := @removelast _) in H;
  rewrite removelast_app in H; try discriminate; simpl in H; rewrite app_nil_r in H;
  rewrite Nat.add_1_r in H;
  rewrite removelast_firstn in H; auto.
Qed.


Lemma combine_distrib: forall A B (a b: list A) (c d : list B), length a = length c -> length b = length d ->
        combine (a ++ b) (c ++ d) = combine a c ++ combine b d.
Proof.
  induction a;
  destruct b, c, d; intuition;
  try inversion H; try inversion H0.
  - simpl; repeat rewrite app_nil_r; trivial.
  - simpl; rewrite IHa; intuition.
Qed.

Lemma partition_sum : forall A (f : A -> nat) (p : A -> bool) l s,
  let (l1, l2) := partition p l in
  fold_right plus s (map f l) = s + fold_right plus 0 (map f l1) + fold_right plus 0 (map f l2).
Proof.
  intros;
  induction l; simpl; [|destruct (partition p l), (p a); simpl]; intuition.
Qed.

Lemma filter_sum_true_total_minus_false : forall A (f : A -> nat) (p : A -> bool) l,
  let sum := fun ll => fold_right plus 0 (map f ll) in
  sum (filter p l) = sum l - sum (filter (fun a => negb (p a)) l).
Proof.
  intros;
  pose proof partition_sum _ f p l 0;
  destruct (partition_filter _ l p);
  destruct (partition _ _); simpl in *; subst; subst sum; intuition.
Qed.

Lemma filter_sum_nonzero : forall l,
  let sum := fold_right plus 0 in
  sum l = sum (filter (fun x => negb (Nat.eqb x 0)) l).
Proof.
  intros;
  induction l; simpl; auto;
  destruct a; simpl; auto.
Qed.

Lemma filter_map : forall A B (l : list A) (f : A -> B) (p : B -> bool),
  filter p (map f l) = map f (filter (fun a => p (f a)) l).
Proof.
  intros;
  induction l; simpl; auto;
  destruct (p _); simpl; congruence.
Qed.

Lemma fold_left_sum_map : forall A (l : list A) (s : nat) (f : nat -> A -> nat) (g : A -> nat)
 (H_f_sum: forall x a, f x a = x + g a), fold_left f l s = fold_left plus (map g l) s.
Proof.
 intros.
 induction l using rev_ind; simpl; auto.
 rewrite map_app.
 rewrite !fold_left_app; simpl.
 rewrite !H_f_sum.
 auto.
Qed.

Lemma fold_left_sum_start : forall A (l : list A) (s x : nat) (f : nat -> A -> nat) (g : A -> nat)
 (H_f_sum: forall x a, f x a = x + g a), fold_left f l (s + x) = fold_left f l s + x.
Proof.
 intros.
 induction l using rev_ind; simpl; auto.
 rewrite !fold_left_app; simpl.
 rewrite !H_f_sum. intuition.
Qed.

Lemma sum_fold_equiv : forall s l, fold_left plus l s = fold_right plus s l.
Proof (fun s => fold_symmetric plus plus_assoc s (plus_comm s)).

Lemma sum_permutation_invariant : forall s l l', Permutation l l' ->
  fold_right plus s l = fold_right plus s l'.
Proof.
  intros s l.
  induction l; intros; simpl.
  - apply Permutation_nil in H. subst. auto.
  - destruct (in_split _ _ (Permutation_in a H (in_eq _ _))) as [l1 [l2]]; subst.
    apply Permutation_cons_app_inv in H.
    rewrite (IHl _ H). clear.
    rewrite !fold_right_app. simpl.
    pose proof fold_left_sum_start _ l1 (fold_right plus s l2) a plus id (fun _ _ => eq_refl).
    rewrite !sum_fold_equiv in H.
    pose proof plus_comm.
    congruence.
Qed.

Lemma sum_permutation_invariant_map : forall A s (l l' : list A) g, Permutation l l' ->
  fold_right plus s (map g l) = fold_right plus s (map g l').
Proof.
  intros A s l.
  induction l; intros; simpl.
  - apply Permutation_nil in H. subst. auto.
  - destruct (in_split _ _ (Permutation_in a H (in_eq _ _))) as [l1 [l2]]; subst.
    apply Permutation_cons_app_inv in H.
    rewrite (IHl _ _ H). clear.
    rewrite !map_app.
    rewrite !fold_right_app. simpl.
    rewrite <- !sum_fold_equiv.
    symmetry.
    rewrite plus_comm.
    erewrite fold_left_sum_start with (g:=id); eauto.
    pose proof plus_comm.
    congruence.
Qed.

Lemma monotonic_contra : forall (A : Type) (f1 f2 : A -> bool),
  monotonic f1 f2 -> monotonic (fun a => negb (f2 a)) (fun a => negb (f1 a)).
Proof.
  unfold monotonic. intros.
  rewrite negb_true_iff, <- not_true_iff_false in *.
  intuition.
Qed.

Lemma filter_monotonic : forall (A : Type) (f1 f2 : A -> bool) (l : list A),
  monotonic f1 f2 -> incl (filter f1 l) (filter f2 l).
Proof.
  intros. pose proof partition_filter _ l.
  destruct (H0 f1) as [H1 _]; rewrite H1; clear H1.
  destruct (H0 f2) as [H1 _]; rewrite H1; clear H1.
  apply partition_monotonic; auto.
Qed.

Lemma filter_sum_true_total_2 : forall A
      (f : A -> nat) (p1 : A -> bool) (p2 : A -> bool)
      (MON: monotonic p1 p2) l,
  let sum := fun ll => fold_right plus 0 (map f ll) in
  sum (filter p2 l) = sum (filter p1 l) + sum (filter (fun a => p2 a && negb (p1 a)) l).
Proof.
  intros.
  induction l; eauto.
  simpl.
  case_eq (p2 a).
  * intros. simpl.
    case_eq (p1 a).
    - intros.
      simpl.
      unfold sum in *.
      simpl. rewrite IHl; rewrite plus_assoc; eauto.
    - intros.
      simpl.
      unfold sum in *; simpl.
      rewrite IHl.
      lia.
  * intros.
    case_eq (p1 a).
    - intros.
      apply MON in H0.
      rewrite H in H0; inversion H0.
    - intros.
      simpl.
      apply IHl.
Qed.

Lemma filter_sum_true_total_minus_false2 : forall A
      (f : A -> nat) (p1 : A -> bool) (p2 : A -> bool)
      (MON: monotonic p1 p2) l,
  let sum := fun ll => fold_right plus 0 (map f ll) in
  sum (filter p1 l) = sum (filter p2 l) - sum (filter (fun a => p2 a && negb (p1 a)) l).
Proof.
  intros.
  pose proof (filter_sum_true_total_2 A f p1 p2 MON l).
  unfold sum in *.
  rewrite H.
  rewrite Nat.add_sub; auto.
Qed.

Lemma nodup_filter: forall A (l : list A) (ND: NoDup l) (P : A -> bool), NoDup (filter P l).
Proof.
  intros.
  induction l; simpl; try apply NoDup_nil.
  case_eq (P a); intros.
  * apply NoDup_cons_iff in ND.
    destruct ND as [N1 N2].
    apply NoDup_cons; eauto.
    intro CONTRA; apply filter_In in CONTRA; destruct CONTRA; eauto.
  * apply NoDup_cons_iff in ND.
    destruct ND as [N1 N2].
    eauto.
Qed.

Lemma incl_cons: forall A l1 l2 (a : A)
                            (EQDEC: forall (a b : A), { a = b } + { a <> b })
                            (NDP: NoDup (a::l1)) (INCL: incl (a::l1) (a::l2)), incl l1 l2.
Proof.
  intros.
  red; red in INCL.
  intros.
  specialize (INCL a0).
  destruct (EQDEC a a0); subst.
  * apply NoDup_cons_iff in NDP; destruct NDP.
    apply H0 in H; inversion H.
  * apply (in_cons a) in H.
    apply INCL in H; simpl in H.
    intuition.
Qed.

Lemma exists_perm_elem_hd: forall A l (a : A) (IN: In a l), exists l', Permutation l (a :: l').
Proof.
  intros.
  apply In_nth with (d:=a) in IN.
  destruct IN as [n [N1 N2]].
  pose proof (nth_split) as SS.
  specialize (SS A n l a N1).
  destruct SS as [l1 [l2 [A1 A2]]].
  exists (l1 ++ l2).
  rewrite N2 in A1.
  rewrite A1.
  symmetry.
  apply Permutation_middle.
Qed.

Lemma incl_cons_inv : forall A (l l' : list A) (a : A), ~ In a l -> incl l (a :: l') -> incl l l'.
Proof.
  unfold incl in *; intros;
  specialize (H0 a0 H1);
  destruct H0; subst; intuition.
Qed.

Lemma fold_sum_incl_map: forall A (l1 l2 : list A) (f : A -> nat)
                                (NDP: NoDup l1)
                                (INCL: incl l1 l2), fold_left plus (map f l1) 0 <= fold_left plus (map f l2) 0.
Proof.
  intros. rewrite !sum_fold_equiv.
  generalize dependent l2.
  induction l1, l2; simpl in *; intuition.
  - exfalso. unfold incl in *. simpl in *. eapply INCL; eauto.
  - inversion NDP; subst. assert (incl l1 (a0 :: l2)) by (unfold incl in *; intuition).
    specialize (IHl1 H2).
    unfold incl in INCL. simpl in *. specialize (INCL a (or_introl eq_refl)).
    destruct INCL; subst.
    + apply incl_cons_inv in H; auto. specialize (IHl1 _ H). intuition.
    + apply in_split in H0. destruct H0 as [l2' [l2'' ?]]; subst.
      erewrite (sum_permutation_invariant_map _ _ (l2' ++ a :: l2''));
      [| symmetry; apply Permutation_middle ]. simpl.
      rewrite plus_assoc. rewrite (plus_comm (f a0) _). rewrite <- plus_assoc.
      change (f a0 + _) with (fold_right plus 0 (map f (a0 :: (l2' ++ l2'')))).
      assert (incl l1 (a0 :: l2' ++ l2'')) by (
      unfold incl in *; intros;
      specialize (H a1 H0);
      rewrite app_comm_cons in *;
      apply in_app_or in H; apply in_or_app; simpl in *; intuition; subst; contradiction).
      specialize (IHl1 _ H0). intuition.
Qed.

Lemma fold_sum_incl: forall l1 l2 (NDP: NoDup l1) (INCL: incl l1 l2), fold_left plus l1 0 <= fold_left plus l2 0.
Proof.
  intros; rewrite <- (map_id l1), <- (map_id l2); apply fold_sum_incl_map; auto.
Qed.

Lemma map_nth_error_None : forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
  nth_error l n = None <-> nth_error (map f l) n = None.
Proof.
  split; intros;
  apply nth_error_None in H; apply nth_error_None; rewrite map_length in *; auto.
Qed.

Lemma firstn_map : forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
  firstn n (map f l) = map f (firstn n l).
Proof.
  intros.
  revert n.
  induction l; intros; simpl.
  - rewrite !firstn_nil. auto.
  - destruct n; simpl; auto. congruence.
Qed.

Lemma nth_error_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B) i,
  nth_error (map f l) i = Some y <-> (exists x : A, f x = y /\ nth_error l i = Some x).
Proof.
  split; intros.
  {
    assert (nth_error (map f l) i <> None) by congruence.
    apply nth_error_Some in H0; rewrite map_length in H0; apply nth_error_Some in H0.
    case_eq (nth_error l i); intros. apply (map_nth_error f) in H1.
    - exists a; intuition; congruence.
    - contradiction.
  }
  {
    destruct H as [a []]. apply (map_nth_error f) in H0. congruence.
  }
Qed.

Lemma filter_empty_iff : forall (A : Type) (p : A -> bool) (l : list A),
  filter p l = [] <-> forall a, In a l -> p a = false.
Proof.
  split; intros.
  {
    induction l; simpl in *; [contradiction |].
    destruct H0; subst.
    destruct (p a); congruence.
    destruct (p a0); try congruence; intuition.
  }
  {
    induction l; simpl; auto;
    rewrite H; intuition.
  }
Qed.

Lemma map_split_r : forall (A B : Type) (l : list (A * B)), map snd l = snd (split l).
Proof.
  intros.
  induction l; simpl; auto.
  destruct a, (split l). simpl in *. congruence.
Qed.

Lemma filter_all: forall A (l : list A) (f : A -> bool) (IN: forall x, In x l -> f x = true),
                    filter f l = l.
Proof.
  ins.
  induction l; ins.
  rewrite IN.
  rewrite IHl; ins.
  apply IN.
  simpl; right; ins.
  ins.
Qed.

Lemma seq_first: forall start len: nat,
    seq start (S len) = start :: seq (S start) len.
Proof.
  auto.
Qed.

Lemma seq_last: forall len start: nat,
    seq start (S len) = seq start len ++ [start + len].
Proof.
  induction len.
  {
    intros.
    rewrite <- plus_n_O.
    auto.
  }
  intros; simpl.
  replace (start + S len) with (S start + len) by lia.
  replace (seq (S start) len ++ [S start + len]) with (seq (S start) (S len)).
  auto.
  apply IHlen.
Qed.

Lemma seq_app : forall len1 len2 start : nat,
      seq start (len1 + len2) = seq start len1 ++ seq (start + len1) len2.
Proof.
  intros.
  induction len2.
  {
    simpl.
    rewrite <- app_nil_end.
    auto.
  }
  rewrite Nat.add_succ_r.
  rewrite seq_last.
  rewrite IHlen2.
  rewrite seq_last.
  assert (start + (len1 + len2) = start + len1 + len2) by lia.
  rewrite H.
  simpl.
  rewrite app_assoc.
  auto.
Qed.

Lemma NoDup_iff: forall A (l1 l2 : list A)
                          (N1: NoDup l1)
                          (N2: NoDup l2)
                          (NIN: forall x, In x l2 -> ~ In x l1), NoDup (l1++l2).
Proof.
  ins.
  generalize dependent l1.
  induction l2; try (rewrite app_nil_r; ins).
  ins.
    rewrite app_nil_r; ins.
  ins.
  assert (PRM: Permutation (a :: l1 ++ l2) (l1 ++ a :: l2))
   by apply Permutation_middle.
  rewrite <- PRM.
  apply IHl2 with (l1 := a :: l1); ins.
  * apply NoDup_cons_iff in N2; des; ins.
  * apply NoDup_cons.
    apply NIN; ins.
    ins.
  * intro CONTRA; des; subst.
    apply NoDup_cons_iff in N2; des; ins.
    apply (NIN x); ins.
Qed.

Lemma all_not_existsb: forall A (l : list A) (f : A -> bool),
                       existsb f l = false -> (forall x, In x l -> f x = false).
Proof.
  intros A l f H;
  induction l; simpl in *; intros; try contradiction;
  rewrite orb_false_iff in H; destruct H;
  destruct H0; subst; auto.
Qed.

Lemma existsb_all_not: forall A (l : list A) (f : A -> bool),
                      (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  intros.
  induction l; simpl; auto.
  apply orb_false_iff.
  split.
  - specialize (H a); destruct H; simpl; auto.
  - apply IHl; intros.
    apply H.
    simpl; intuition.
Qed.

Definition list_max (l : list nat) : nat := fold_right max 0 l.

Lemma list_max_le : forall l x, In x l -> x <= list_max l.
Proof.
  pose proof Nat.le_max_r;
  pose proof Nat.le_max_l;
  induction l; simpl in *; intuition; subst; auto;
  transitivity (list_max l); auto.
Qed.

Definition is_prefix_of {A} (p l : list A) := { s | p ++ s = l }.

Lemma firstn_prefix: forall {A} (l : list A) i, is_prefix_of (firstn i l) l.
Proof.
  unfold is_prefix_of.
  intros. exists (skipn i l). apply firstn_skipn.
Qed.

Lemma list_indexing_eq : forall A (l : list A) d, l = map (fun i => nth i l d) (seq 0 (length l)).
Proof.
 intros.
 induction l using rev_ind; simpl; auto.
 rewrite app_length, seq_app; simpl.
 rewrite map_app. simpl. rewrite app_nth2, minus_diag; auto; simpl.
 rewrite IHl at 1; clear IHl; f_equal.
 apply map_ext_in; intros. rewrite app_nth1; auto.
 apply in_seq in H; intuition.
Qed.

Definition rev_list_rect : forall (A : Type) (P : list A -> Type),
  P [] -> (forall (a : A) (l : list A), P (rev l) -> P (rev (a :: l))) -> forall l : list A, P (rev l) :=
  fun (A : Type) (P : list A -> Type) (H : P [])
  (H0 : forall (a : A) (l : list A), P (rev l) -> P (rev (a :: l))) (l : list A) =>
  list_rect (fun l0 : list A => P (rev l0)) H (fun (a : A) (l0 : list A) (IHl : P (rev l0)) => H0 a l0 IHl) l.

Definition rev_rect : forall (A : Type) (P : list A -> Type),
  P [] -> (forall (x : A) (l : list A), P l -> P (l ++ [x])) -> forall l : list A, P l :=
  fun (A : Type) (P : list A -> Type) (H : P []) (H0 : forall (x : A) (l : list A), P l -> P (l ++ [x]))
  (l : list A) =>
  (fun E : rev (rev l) = l =>
    eq_rect (rev (rev l)) (fun l0 : list A => P l0)
    (rev_list_rect _ P H (fun (a : A) (l0 : list A) (H1 : P (rev l0)) => H0 a (rev l0) H1) (rev l)) l E)
    (rev_involutive l).
