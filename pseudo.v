(** # <img src="../figs/num_relations.svg"> # *)

From SN Require Import base equiv add.

Definition zz := [singleton 0, singleton 0].

Definition g0 := [singleton zz, ∅].

Theorem g0_is_0 : g0 ≡ 0.
Proof.
  do 2 constructor; try intros [].
  constructor; right.
  exists tt.
  constructor; intros [].
Qed.

Theorem zz_not_num : ~ num zz.
Proof.
  intros [_ [_ H]].
  apply (sle_not_snge _ _ (sle_refl 0)), (H tt tt).
Qed.

Theorem g0_not_num : ~ num g0.
Proof.
  intros [H _].
  apply zz_not_num, (H tt).
Qed.

Definition g1 := [singleton g0, ∅].

Theorem g1_not_num : ~ num g1.
Proof.
  intros [H _].
  apply g0_not_num, (H tt).
Qed.

Theorem g1_is_1 : g1 ≡ 1.
Proof.
  apply eqs_eq.
  split.
  - split; exists tt; apply g0_is_0.
  - apply set_eq_refl.
Qed.

Goal ∃ x, bound x ∧ ~ num x.
  exists g1. split.
  - unfold bound, lbound, rbound, g1, singleton.
    split; intros.
    + rewrite g0_is_0, g1_is_1. constructor; intros [].
    + destruct j.
  - exact g1_not_num.
Qed.

Definition weak_num (x : surreal) : Prop :=
  match x with
  | snlr L R l r =>
    (∀ i : L, ∀ j : R, l i ≱ r j)
  end.

Goal ∀ x, lbound x → weak_num x.
  intros [L R l r] H i j.
  apply trans with [l, r]; auto.
Qed.

Goal ∃ x, rbound x ∧ ~ lbound x.
  exists g0. split.
  - intros [].
  - intros H. specialize (H tt).
    rewrite g0_is_0 in H.
    sinv H.
    specialize (H tt).
    apply (sle_not_snge _ _ (sle_refl 0)), H.
Qed.

Definition g0' := [∅, singleton zz].

Theorem g0'_is_0 : g0' ≡ 0.
Proof.
  do 2 constructor; try intros [].
  constructor; left.
  exists tt.
  constructor; intros [].
Qed.

Goal ∀ x, rbound x → weak_num x.
  intros [L R l r] H i j.
  apply trans2 with [l, r]; auto.
Qed.

Goal ∃ x, lbound x ∧ ~ rbound x.
  exists g0'. split.
  - intros [].
  - intros H. specialize (H tt).
    rewrite g0'_is_0 in H.
    sinv H.
    specialize (H0 tt).
    apply (sle_not_snge _ _ (sle_refl 0)), H0.
Qed.

Definition oz := [singleton 1, singleton 0].

Theorem zz_ngeq_oz : zz ≱ oz.
Proof.
  constructor. left. exists tt.
  split; intros. apply cmp_m1_0_1.
  destruct j.
Qed.

Definition zzoz := [singleton zz, singleton oz].

Theorem zzoz_is_0 : zzoz ≡ 0.
Proof.
  do 2 constructor; try intros []; constructor.
  - right. exists tt. reflexivity.
  - left. exists tt. split; intros [].
Qed.

Goal ∃ x, weak_num x ∧ ~ lbound x ∧ ~ rbound x.
  exists zzoz. split.
  - intros i j. apply zz_ngeq_oz.
  - split; intros H; specialize (H tt); rewrite zzoz_is_0 in H; apply (sle_not_snge _ _ (sle_refl 0)).
    + apply trans2 with zz; auto.
      destruct (range_aux zz) as [H1 _].
      apply (H1 tt).
    + apply trans with oz; auto.
      destruct (range_aux oz) as [_ H2].
      apply (H2 tt).
Qed.

Definition zzzz := [singleton zz, singleton zz].

Theorem zzzz_is_0 : zzzz ≡ 0.
Proof.
  do 2 constructor; try intros []; constructor; [right | left]; exists tt; reflexivity.
Qed.

From Stdlib Require Import Classical.

Theorem simplicity : forall {Lx Rx Ly Ry lx ly rx ry},
  (∀ i : Lx, lx i ≱ [ly, ry]) → (∀ j : Rx, [ly, ry] ≱ rx j) →
  (∀ j : Ly, ∃ i, ly j ≤ lx i) →
  (∀ j : Ry, ∃ i, ry j ≥ rx i) →
  [lx, rx] ≡ [ly, ry].
Proof.
  do 2 split; try assumption; intros; solve_snge; auto.
Qed.

Lemma not_all_ex_ex_all_not : forall {Ly Lx ly lx} (R : surreal → surreal → Prop),
  (~ (∀ j : Ly, ∃ i : Lx, R (ly j) (lx i)) → ∃ j, ∀ i, ~ R (ly j) (lx i)) ∧
  (~ (∀ j : Ly, ∃ i : Lx, R (lx i) (ly j) ) → ∃ j, ∀ i, ~ R (lx i) (ly j)).
Proof.
  split; intros.
  all: apply not_all_not_ex; intros H0; apply H; clear H;
  intros; apply not_all_not_ex; auto.
Qed.

Theorem rec_num : ∀ Lx Rx (lx : Lx → surreal) (rx : Rx → surreal) y,
  (∀ i : Lx, lx i ≱ y) → (∀ j : Rx, y ≱ rx j) →
  (num y) →
  (∃ z, num z ∧ [lx, rx] ≡ z).
Proof.
  intros Lx Rx lx rx y H1 H2 Hnum.
  induction y as [Ly Ry ly IH1 ry IH2].
  destruct (classic (∀ j : Ly, ∃ i, ly j ≤ lx i)), (classic (∀ j : Ry, ∃ i, ry j ≥ rx i)).
  1: exists [ly, ry]; split; auto. apply simplicity; auto.
  1,3: clear -H1 Hnum IH2 H0; inversion Hnum as [_ [Hnum' _]].
  3: clear -H2 Hnum IH1 H;  inversion Hnum as [Hnum' _]; rename IH1 into IH2, H into H0.
  all: apply not_all_ex_ex_all_not in H0; destruct H0 as [j H0].
  all: apply IH2 with j; auto; intros i; try (apply not_sle_snge; apply H0).
  1,2: apply trans2 with [ly, ry].
  5:apply trans with [ly, ry].
  all: auto; apply num_bound in Hnum; apply Hnum.
Qed.

Definition geq_num (x : surreal) : {y : surreal | num y ∧ x ≤ y}.
  induction x as [L R l IH1 r _].
  exists [(fun l => proj1_sig (IH1 l)), ∅].
  split.
  - split.
    intros i. apply (proj2_sig (IH1 i)).
    split. intros []. intros _ [].
  - constructor; intros i; [| destruct i].
    solve_snge.
    exists i. apply (proj2_sig (IH1 i)).
Defined.

Definition leq_num (x : surreal) : {y : surreal | num y ∧ y ≤ x}.
  induction x as [L R l _ r IH2].
  exists [∅, (fun r => proj1_sig (IH2 r))].
  split.
  - split.
    intros [].
    split. intros i. apply (proj2_sig (IH2 i)).
    intros [].
  - constructor; intros i; [destruct i|].
    solve_snge.
    exists i. apply (proj2_sig (IH2 i)).
Defined.
