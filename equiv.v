From Stdlib Require Import Setoid.
From SN Require Import base.

Definition seq x y := (x ≤ y) ∧ (x ≥ y).

Hint Unfold seq : core.

Infix "≡" := seq (at level 70) : surreal_scope.

Lemma seq_refl : forall x : surreal, x ≡ x.
  intros. split; apply sle_refl.
Qed.

Lemma seq_sym : forall x y : surreal, x ≡ y -> y ≡ x.
  intros. destruct H. split; auto.
Qed.

Lemma seq_trans : forall x y z : surreal, x ≡ y -> y ≡ z -> x ≡ z.
  intros. destruct H. destruct H0.
  split; eapply trans; eauto.
Qed.

Add Relation surreal seq
  reflexivity proved by seq_refl
  symmetry proved by seq_sym
  transitivity proved by seq_trans
  as seq_rel.

Add Relation surreal sle
  reflexivity proved by sle_refl
  transitivity proved by (λ x y z, match trans x y z with
    | conj H _ => H
    end)
  as sle_rel.

Add Morphism sle with signature seq ==> seq ==> iff as sle_mor.
Proof with auto.
  intros x1 x2 [H1 H2] y1 y2 [H3 H4].
  split; intros.
  - transitivity x1...
    transitivity y1...
  - transitivity x2...
    transitivity y2...
Qed.

Add Morphism snge with signature seq ==> seq ==> iff as snge_mor.
Proof with eauto.
  intros x1 x2 [H1 H2] y1 y2 [H3 H4].
  split; intros.
  all: eapply trans...
  all: eapply trans2...
Qed.

Definition union {A B} (f : A → surreal) (g : B → surreal) :=
  λ x : A + B, match x with
    | inl a => f a
    | inr b => g b
    end.

Infix "∪" := union (at level 50).

Hint Unfold union : core.

(** T7 *)
Theorem bound_eq: forall x y : surreal,
  match x, y with
  | [lx, rx], [ly, ry] =>
    (∀ i, ly i ≱ x) → (∀ j, x ≱ ry j) → x ≡ [lx ∪ ly, rx ∪ ry]
  end.
Proof.
  intros [Lx Rx lx rx] [Ly Ry ly ry] Hl Hr. split.
  - apply Sle; intros.
    + solve_snge. exists (inl i). reflexivity.
    + destruct j as [j | j].
      * solve_snge. exists j. reflexivity.
      * apply Hr.
  - apply Sle; intros.
    + destruct i as [i | i].
      * simpl. auto.
      * apply Hl.
    + solve_snge. exists (inl j). reflexivity.
Qed.

Reserved Notation "x ≡s y" (at level 70).

Inductive eqs : surreal → surreal → Prop :=
  | eqs_intro : ∀ Lx Rx Ly Ry (lx : Lx → surreal) (rx : Rx → surreal)
    (ly : Ly → surreal) (ry : Ry → surreal),
    (∀ i, ∃ j, lx i ≡s ly j) → (∀ j, ∃ i, lx i ≡s ly j) →
    (∀ i, ∃ j, rx i ≡s ry j) → (∀ j, ∃ i, rx i ≡s ry j) →
    eqs [lx, rx] [ly, ry]
where "x ≡s y" := (eqs x y).

Theorem eqs_refl : ∀ x : surreal, x ≡s x.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  split; intros i; exists i; auto.
Qed.

Ltac ex_eq i :=
  match type of i with
  | ?T => match goal with
    | H: ∀_:T, ∃_,_ |- _ => destruct (H i) as [j Hj]
    end
  end.

Theorem eqs_sym : ∀ x y : surreal, x ≡s y → y ≡s x.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  intros [Ly Ry ly ry] H.
  eqdep_inv H.
  split; intros i; ex_eq i; exists j; auto.
Qed.

Theorem eqs_trans : ∀ x y z : surreal,
  x ≡s y → y ≡s z → x ≡s z.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  destruct y as [Ly Ry ly ry].
  destruct z as [Lz Rz lz rz].
  intros H1 H2. eqdep_inv H1. eqdep_inv H2.
  split; intros i; ex_eq i;
  match type of j with
  | ?T => match goal with
  | |- ∃_:?U,_ => match goal with
    | H: ∀_:T, ∃_:U,_ |- _ => destruct (H j) as [k Hk]
    end
  end
  end; exists k; eauto.
Qed.

Add Relation surreal eqs
  reflexivity proved by eqs_refl
  symmetry proved by eqs_sym
  transitivity proved by eqs_trans as eqs_rel.

Theorem eqs_eq : ∀ x y : surreal, x ≡s y → x ≡ y.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  intros [Ly Ry ly ry] H. eqdep_inv H.
  do 2 split; intros i; solve_snge; ex_eq i;
  exists j; try apply IH1; try apply IH2; auto.
Qed.

Add Morphism seq with signature eqs ==> eqs ==> iff as seq_mor.
Proof.
  split; intros;
  [rewrite <- (eqs_eq x y H), <- (eqs_eq x0 y0 H0) |
   rewrite (eqs_eq x y H), (eqs_eq x0 y0 H0)]; auto.
Qed.

Hint Resolve eqs_eq : core.

Definition set_eq {A} {B} (f : A → surreal) (g : B → surreal) :=
  (∀ i, ∃ j, f i ≡ g j) ∧ (∀ j, ∃ i, f i ≡ g j).

Theorem set_eq_union : ∀ A B C D (f : A → surreal) (g : B → surreal) (f' : C → surreal) (g' : D → surreal),
  set_eq f f' → set_eq g g' → set_eq (f ∪ g) (f' ∪ g').
Proof.
  intros. unfold set_eq in *. destruct H, H0.
  split; intros [i|i];
  ex_eq i; try exists (inl j); try exists (inr j); auto.
Qed.

Theorem set_eq_seq : ∀ A B C D (f : A → surreal) (g : B → surreal) (f' : C → surreal) (g' : D → surreal),
  set_eq f f' →
  set_eq g g' →
  [f, g] ≡ [f', g'].
Proof.
  intros; unfold set_eq in *; destruct H, H0.
  do 2 split; intros i; ex_eq i; solve_snge; exists j; apply Hj.
Qed.
