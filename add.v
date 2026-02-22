From Stdlib Require Import Setoid FunctionalExtensionality.
From SN Require Import base equiv.

(** Chapter 8 *)

Fixpoint sadd (x : surreal) : surreal → surreal :=
  match x with
  | [lx, rx] =>
    fix sadd_y (y : surreal) : surreal :=
      match y with
      | [ly, ry] =>
        [ (λ i, sadd (lx i) y) ∪ λ i, sadd_y (ly i),
          (λ j, sadd (rx j) y) ∪ λ j, sadd_y (ry j) ]
      end
  end.

Infix "+" := sadd : surreal_scope.

Lemma sadd_rewrite : ∀ Lx Rx Ly Ry (lx : Lx → surreal) (rx : Rx → surreal)
  (ly : Ly → surreal) (ry : Ry → surreal),
  [lx, rx] + [ly, ry] =
    [ (λ i, lx i + [ly, ry]) ∪ λ i, [lx, rx] + ly i,
      (λ j, rx j + [ly, ry]) ∪ λ j, [lx, rx] + ry j ].
Proof. reflexivity. Qed.

Module AddExample1.

Definition explore_add x y := ∃ L R (l : L → surreal) (r : R → surreal),
  x + y = [l, r] /\ [l, r] = 0.

Ltac explore_add := unfold explore_add; do 4 eexists; split.

Definition ess' := ∅ ∪ ∅.
Definition zero' := [ess', ess'].

Ltac solve_add :=
  match goal with
  | |- _ + _ = ?tm => unfold tm
  end; rewrite sadd_rewrite; f_equal; apply functional_extensionality;
  intros p; destruct p; match goal with
  | tm : Empty_set |- _ => destruct tm
  | tm : unit |- _ => unfold singleton, union
  end; auto with surreal.

Theorem szpz : 0 + 0 = zero'. solve_add. Qed.
Hint Resolve szpz : surreal.

Definition one' := [singleton zero' ∪ ∅, ess'].
Definition one'' := [∅ ∪ singleton zero', ess'].

Theorem sopz : 1 + 0 = one'. solve_add. Qed.
Hint Resolve sopz : surreal.

Theorem szpo : 0 + 1 = one''. solve_add. Qed.
Hint Resolve szpo : surreal.

Definition opo := [singleton one'' ∪ singleton one', ess'].

Theorem sopo : 1 + 1 = opo. solve_add. Qed.

End AddExample1.

(** Chapter 9 *)

Theorem sadd_comm_eqs : ∀ x y : surreal, x + y ≡s y + x.
Proof.
  induction x as [Lx Rx lx IHlx rx IHRx].
  induction y as [Ly Ry ly IHly ry IHRy].
  split.
  all: eapply set_eq_trans; [apply set_eq_union_comm | ]; apply union_mor; split.
  all: eauto.
Qed.

(** T9 *)
Corollary sadd_comm : ∀ x y : surreal, x + y ≡ y + x.
Proof. intros. apply eqs_eq. apply sadd_comm_eqs. Qed.

Lemma sadd_sle_comm : ∀ x y : surreal,
  x + y ≤ y + x.
Proof. apply sadd_comm. Qed.

Theorem sadd_zero_eqs : ∀ x : surreal, x + 0 ≡s x.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  split.
  all: split; [intros [p | []] | intros p].
  all: try exists p; try exists (inl p); simpl; auto.
Qed.

(** T10 *)
Corollary sadd_zero : ∀ x : surreal, x + 0 ≡ x.
Proof. intros. apply eqs_eq. apply sadd_zero_eqs. Qed.

(** Chapter 10 *)

Theorem sadd_assoc_eqs : ∀ x y z : surreal,
  (x + y) + z ≡s x + (y + z).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  induction z as [Lz Rz lz IH5 rz IH6].
  do 2 split.
  all: try (intros [[p|p]|p];
    [exists (inl p) | exists (inr (inl p)) | exists (inr (inr p))]).
  all: try (intros [p|[p|p]];
    [exists (inl (inl p)) | exists (inl (inr p)) | exists (inr p)]).
  all: cbn [union].
  all: auto.
Qed.

(** T11 *)
Corollary sadd_assoc : ∀ x y z : surreal,
  (x + y) + z ≡ x + (y + z).
Proof. intros. apply eqs_eq. apply sadd_assoc_eqs. Qed.

Lemma sadd_mono_aux : forall x y z : surreal,
  (x ≤ y → x + z ≤ y + z) ∧ (x ≱ y → x + z ≱ y + z).
Proof with auto.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  induction z as [Lz Rz lz IH5 rz IH6].
  do 2 rewrite sadd_rewrite.
  split; intros.
  - split.
    all: intros [p|p];
      [sinv H; rewrite <- sadd_rewrite | solve_snge; exists (inr p)];
      cbn [union].
    + apply IH1...
    + apply IH5...
    + apply IH4...
    + apply IH6...
  - split. do 2 rewrite <- sadd_rewrite.
    sinv H.
    + left. exists (inl i). cbn [union]. apply IH3...
    + right. exists (inl j). cbn [union]. apply IH2...
Qed.

(** T13 *)
Lemma sadd_sle_mono_r : forall x y z : surreal,
  x ≤ y → x + z ≤ y + z.
Proof. apply sadd_mono_aux. Qed.

Lemma sadd_sle_mono : forall x y z w : surreal,
  x ≤ y → z ≤ w → x + z ≤ y + w.
Proof with auto using sadd_sle_mono_r, sadd_sle_comm.
  intros.
  transitivity (y + z)...
  transitivity (z + y)...
  transitivity (w + y)...
Qed.

Lemma sadd_snge_mono_r : forall x y z : surreal,
  x ≱ y → x + z ≱ y + z.
Proof. apply sadd_mono_aux. Qed.

Lemma sadd_snge_mono_l : forall x y z : surreal,
  x ≱ y → z + x ≱ z + y.
Proof.
  intros.
  rewrite (sadd_comm z x), (sadd_comm z y).
  apply sadd_snge_mono_r. auto.
Qed.

(* T12 *)
Add Morphism sadd with signature
  (seq ==> seq ==> seq) as sadd_mor.
Proof.
  intros x1 x2 [Hxy Hyx] y1 y2 [Hyz Hzy].
  auto using sadd_sle_mono.
Qed.

Definition ssub x y := x + (- y).
Infix "-" := ssub : surreal_scope.

(** T15 *)
Theorem ssub_diag : forall x : surreal, x - x ≡ 0.
Proof.
  unfold ssub.
  induction x as [Lx Rx lx IH1 rx IH2].
  cbn [sopp].
  rewrite sadd_rewrite.
  do 2 split; intros []; cbn [union].
  - rename l into p.
    eapply trans2. 2: apply (IH1 p).
    destruct (lx p) as [LLx RRx llx rrx] eqn:E0.
    rewrite sadd_rewrite.
    solve_snge. exists (inr p). cbn [union].
    rewrite <- E0. reflexivity.
  - eapply trans2. 2: apply (IH2 r).
    apply sadd_snge_mono_r. auto.
  - rename r into p.
    eapply trans. 1: apply (IH2 p).
    destruct (rx p) as [LRx RRy lrx rry] eqn:E0.
    rewrite sadd_rewrite.
    solve_snge. exists (inr p). cbn [union].
    rewrite <- E0. reflexivity.
  - eapply trans. 1: apply (IH1 l).
    apply sadd_snge_mono_r. auto.
Qed.

(** T14 *)
Theorem sadd_sle_mono_r_rev : forall x y z : surreal,
  x + z ≤ y + z → x ≤ y.
Proof.
  intros.
  rewrite <- (sadd_zero x); rewrite <- (sadd_zero y).
  rewrite <- (ssub_diag z).
  unfold ssub.
  do 2 rewrite <- sadd_assoc.
  apply sadd_sle_mono_r. auto.
Qed.

Lemma sadd_sle_mono_l_rev : forall x y z : surreal,
  z + x ≤ z + y → x ≤ y.
Proof.
  intros.
  apply sadd_sle_mono_r_rev with (z := z).
  rewrite (sadd_comm x z), (sadd_comm y z).
  assumption.
Qed.

(** T16 *)
Theorem sopp_involutive : forall x : surreal,
  (- (- x)) = x.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  cbn [sopp].
  f_equal; apply functional_extensionality; auto.
Qed.

(* T19 *)
Lemma sopp_sle_mono : forall x y : surreal,
  x ≤ y → (- y) ≤ (- x).
Proof.
  intros.
  apply sadd_sle_mono_l_rev with x.
  transitivity (y + (- y)).
  apply sadd_sle_mono_r; auto.
  rewrite (ssub_diag x), (ssub_diag y).
  reflexivity.
Qed.

Add Morphism sopp with signature
  (seq ==> seq) as sopp_mor.
Proof.
  split; apply sopp_sle_mono; apply H.
Qed.

Add Morphism ssub with signature
  (seq ==> seq ==> seq) as ssub_mor.
Proof.
  intros. unfold ssub.
  rewrite H, H0. reflexivity.
Qed.

Theorem sadd_num : ∀ x y, num x → num y → num (x + y).
Proof with
  try apply sadd_snge_mono_l; try apply sadd_snge_mono_r; auto.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  intros Hx Hy.
  inversion Hx as [? []]; inversion Hy as [? []].
  rewrite sadd_rewrite. cbn [num].
  intuition; cbn [union]...
  1: apply trans with (y:=[lx, rx] + [ly, ry])...
  2: apply trans2 with (y:=[lx, rx] + [ly, ry])...
  all: apply sadd_sle_mono; try reflexivity.
  all: apply num_bound in Hx; destruct Hx; auto.
Qed.
