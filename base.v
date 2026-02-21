From Stdlib Require Export Utf8_core.

Ltac inv H := inversion H; clear H; subst.

Inductive surreal :=
  | snlr L R (l : L → surreal) (r : R → surreal).

Declare Scope surreal_scope.

Open Scope surreal_scope.

Notation "[ l , r ]" := (snlr _ _ l r).

Reserved Notation "x ≤ y" (at level 70).
Reserved Notation "x ≱ y" (at level 70).

Inductive sle : surreal → surreal → Prop :=
| Sle :
    ∀ (Lx Rx Ly Ry : Type)
      (lx : Lx → surreal) (rx : Rx → surreal)
      (ly : Ly → surreal) (ry : Ry → surreal),
      (∀ i : Lx, lx i ≱ [ly, ry]) →
      (∀ j : Ry, [lx, rx] ≱ ry j) →
      [lx, rx] ≤ [ly, ry]
with snge : surreal → surreal → Prop :=
| Snge :
    ∀ (Lx Rx Ly Ry : Type)
      (lx : Lx → surreal) (rx : Rx → surreal)
      (ly : Ly → surreal) (ry : Ry → surreal),
      (∃ i : Ly, [lx, rx] ≤ ly i) ∨
      (∃ j : Rx, rx j ≤ [ly, ry]) →
      [lx, rx] ≱ [ly, ry]
where "x ≤ y" := (sle x y) : surreal_scope
and "x ≱ y" := (snge x y) : surreal_scope.


Notation "x ≥ y" := (y ≤ x) (only parsing, at level 70) : surreal_scope.
Notation "x ≰ y" := (y ≱ x) (only parsing, at level 70) : surreal_scope.

Notation "x < y" := (x ≤ y ∧ x ≱ y) (at level 70, no associativity) : surreal_scope.
Notation "x > y" := (y < x) (at level 70, no associativity) : surreal_scope.

From Stdlib Require Import Eqdep.

Lemma sle_inv_dep : forall Lx Rx Ly Ry
  (lx : Lx → surreal) (rx : Rx → surreal)
  (ly : Ly → surreal) (ry : Ry → surreal),
  [lx, rx] ≤ [ly, ry] →
  (∀ i : Lx, lx i ≱ [ly, ry]) ∧
  (∀ j : Ry, [lx, rx] ≱ ry j).
Proof.
  intros.
  inv H.
  apply inj_pair2 in H3, H4, H7, H8; subst. auto.
Qed.

Lemma snge_inv_dep : forall Lx Rx Ly Ry
  (lx : Lx → surreal) (rx : Rx → surreal)
  (ly : Ly → surreal) (ry : Ry → surreal),
  [lx, rx] ≱ [ly, ry] →
  (∃ i : Ly, [lx, rx] ≤ ly i) ∨
  (∃ j : Rx, rx j ≤ [ly, ry]).
Proof.
  intros. inv H.
  apply inj_pair2 in H3, H4, H7, H8; subst. auto.
Qed.

Ltac sinv H := match type of H with
  |  _ ≤ _ => apply sle_inv_dep in H; destruct H
  |  _ ≱ _ => apply snge_inv_dep in H; destruct H as [[?i] | [?j]]
end.

Lemma sle_not_snge:
  ∀ x y : surreal, x ≤ y → ~ y ≱ x.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  intros Hle Hnle.
  sinv Hle. sinv Hnle.
  - (* Oops! There is no occurence of y ≤ _ on the left side *)
Abort.

Lemma sle_not_snge:
  ∀ x y : surreal, x ≤ y → ~ y ≱ x.
Proof.
  intros x y.
  apply proj1 with (y ≤ x → ~ x ≱ y).
  revert y.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  split; intros Hle Hnge; sinv Hle; sinv Hnge.
  1: destruct (IH1 i [ly, ry]).
  2: destruct (IH4 j).
  3: destruct (IH3 i).
  4: destruct (IH2 j [ly, ry]).
  all: intuition.
Qed.

From Stdlib Require Import Classical.

Lemma not_snge_sle :
  ∀ x y : surreal, ~ x ≱ y -> y ≤ x.
Proof.
  intros x y.
  apply proj2 with (~ y ≱ x -> x ≤ y).
  revert y.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  split; intros HNnge; constructor; intros; apply NNPP; intros Hnge; apply HNnge; constructor.
  1: destruct (IH1 i [ly, ry]) as [_ H].
  2: destruct (IH4 j) as [_ H].
  3: destruct (IH3 i) as [H _].
  4: destruct (IH2 j [ly, ry]) as [H _].
  all: try apply H in Hnge; eauto.
Qed.

Corollary not_sle_snge :
  ∀ x y : surreal, ~ x ≤ y → y ≱ x.
Proof.
  intros. apply NNPP. intros HNnge.
  auto using not_snge_sle.
Qed.

Theorem sle_iff :
  ∀ (Lx Rx Ly Ry : Type)
    (lx : Lx → surreal) (rx : Rx → surreal)
    (ly : Ly → surreal) (ry : Ry → surreal),
    [lx, rx] ≤ [ly, ry] ↔
    (∀ i : Lx, ~ ([ly, ry] ≤ lx i)) ∧
    ∀ j : Ry, ~ (ry j ≤ [lx, rx]).
Proof.
  split; intros.
  - apply sle_inv_dep in H.
    split; intro; intros Hle.
    1: specialize sle_not_snge with [ly, ry] (lx i).
    2: specialize sle_not_snge with (ry j) [lx, rx].
    all: intuition.
  - constructor; intros.
    1: specialize not_sle_snge with [ly, ry] (lx i).
    2: specialize not_sle_snge with (ry j) [lx, rx].
    all: destruct H; auto.
Qed.

Definition lbound := λ x, match x with | snlr L R l r => ∀ i : L, l i ≤ [l, r] end.
Definition rbound := λ x, match x with | snlr L R l r => ∀ j : R, [l, r] ≤ r j end.
Definition bound := λ x, lbound x ∧ rbound x.

Fixpoint num (s : surreal) : Prop :=
  match s with
  | snlr L R l r =>
    (∀ i : L, num (l i)) ∧
    (∀ j : R, num (r j)) ∧
    (∀ i : L, ∀ j : R, l i ≱ r j)
  end.

Notation "∅" := (λ e : Empty_set, match e with end).

Notation "0" := [∅, ∅].

Definition singleton (x : surreal) := λ _ : unit, x.

Notation "1" := [singleton 0, ∅].

Fixpoint sopp x :=
  match x with
  | [lx, rx] => [ λ j, sopp (rx j), λ i, sopp (lx i) ]
  end.

Notation "( - x )" := (sopp x) : surreal_scope.

From Stdlib Require Import FunctionalExtensionality.

Example opp_0 : (-0) = 0.
Proof.
  simpl. f_equal; extensionality i; tauto.
Qed.

Example neg_one : (-1) = [∅, singleton 0].
Proof.
  simpl.
  f_equal. extensionality i; tauto.
  rewrite <- opp_0. reflexivity.
Qed.

Proposition num_0_1_m1 : num 0 /\ num 1 /\ num (-1).
Proof.
  repeat split; intros [].
  intros [].
Qed.

Proposition cmp_m1_0_1 :
  (-1) < 0 ∧ 0 < 1 ∧ (-1) < 1.
Proof with try intros [].
  rewrite neg_one.
  repeat split...
  1: right.
  2,3: left.
  all: exists tt; split...
Qed.

(** Chapter 4 Bad Numbers *)

(** T1 T5 and T6 *)
Theorem trans :
  ∀ x y z : surreal,
    (x ≤ y → y ≤ z → x ≤ z) ∧
    (x ≱ y → y ≤ z → x ≱ z) ∧
    (x ≤ y → y ≱ z → x ≱ z).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  induction z as [Lz Rz lz IH5 rz IH6].
  split; [| split]; intros Hxy Hyz.
  - constructor; intros.
    + sinv Hxy.
      specialize (IH1 i [ly, ry] [lz, rz]).
      intuition.
    + sinv Hyz.
      specialize (IH6 j).
      intuition.
  - sinv Hxy.
    + sinv Hyz.
      specialize (IH3 i [lz, rz]).
      intuition.
    + constructor; right.
      specialize (IH2 j [ly, ry] [lz, rz]).
      exists j. intuition.
  - sinv Hyz.
    + constructor; left.
      specialize (IH5 i).
      exists i. intuition.
    + sinv Hxy.
      specialize (IH4 j [lz, rz]).
      intuition.
Qed.

Corollary trans2 :
  ∀ x y z : surreal,
    x ≱ y → y ≤ z → x ≱ z.
Proof. apply trans. Qed.

(** Chapter 5 Progress *)

(** This lemma doesn't rely on eqdep *)
Lemma range_aux : forall x : surreal,
  match x with
  | snlr L R l r =>
      (∀ i : L, l i ≱ [l, r]) ∧
      (∀ j : R, [l, r] ≱ r j)
  end.
Proof.
  induction x as [L R l IH1 r IH2]; split; intros.
  - specialize IH1 with i.
    destruct (l i) as [L0 R0 l0 r0] eqn:E.
    destruct IH1.
    constructor. left. exists i.
    rewrite E. split; auto.
  - specialize IH2 with j.
    destruct (r j) as [L0 R0 l0 r0] eqn:E.
    destruct IH2.
    constructor. right. exists j.
    rewrite E. split; auto.
Qed.

Lemma range : forall Lx Rx (lx : Lx → surreal) (rx : Rx → surreal),
  (∀ i : Lx, lx i ≱ [lx, rx]) ∧
  (∀ j : Rx, [lx, rx] ≱ rx j).
Proof.
  intros. specialize range_aux with [lx, rx]. auto.
Qed.

Lemma range_l : forall Lx Rx (lx : Lx → surreal) (rx : Rx → surreal), (∀ i : Lx, lx i ≱ [lx, rx]). apply range. Qed.
Lemma range_r : forall Lx Rx (lx : Lx → surreal) (rx : Rx → surreal), (∀ j : Rx, [lx, rx] ≱ rx j). apply range. Qed.

Hint Resolve range_l range_r : core.

(** T3 *)
Theorem sle_refl : forall x : surreal, x ≤ x.
Proof.
  intros [Lx Rx lx rx].
  destruct (range Lx Rx lx rx).
  constructor; auto.
Qed.

(** T2 *)
Theorem num_bound : forall x,
  num x → bound x.
Proof with auto.
  induction x as [L R l IH1 r IH2]; split; destruct H as [H1 [H2 Hnge]]; simpl; intros.
  - specialize (IH1 i (H1 i)). specialize (Hnge i).
    destruct (l i) as [L0 R0 l0 r0] eqn:E.
    constructor...
    intros; eapply trans.
    + apply IH1.
    + rewrite <-E...
  - specialize (IH2 j (H2 j)).
    specialize Hnge with (j:=j).
    destruct (r j) as [L0 R0 l0 r0] eqn:E.
    constructor...
    intros; eapply trans2.
    2: apply IH2.
    rewrite <-E...
Qed.

(** T4 *)
Theorem bound_snge_sle : ∀ x y : surreal, lbound x → rbound y → x ≱ y → x ≤ y.
  intros [Lx Rx lx rx] [Ly Ry ly ry].
  constructor; intros.
  1: eapply trans.
  3: eapply trans2.
  all: eauto.
Qed.

Ltac solve_snge := match goal with
  | |- ?X ≱ [?Y, ?Z] =>
      destruct X as [tacL tacR tacl tacr] eqn:tacE; constructor; left; rewrite <-tacE in *; clear tacL tacR tacl tacr tacE
  | |- [?X, ?Y] ≱ ?Z =>
      destruct Z as [tacL tacR tacl tacr] eqn:tacE; constructor; right; rewrite <-tacE in *; clear tacL tacR tacl tacr tacE
  | _ => fail 1 "Goal is not of the form x ≱ y with x or y a surreal number constructor"
  end.