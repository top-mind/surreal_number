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

Definition set_eq {A B} (f : A → surreal) (g : B → surreal) :=
  (∀ i, ∃ j, f i ≡ g j) ∧ (∀ j, ∃ i, f i ≡ g j).

Lemma set_eq_refl :
  ∀ {A} (f : A → surreal), set_eq f f.
Proof. split; intros i; exists i; reflexivity. Qed.

Lemma set_eq_sym :
  ∀ {A B} (f : A → surreal) (g : B → surreal),
  set_eq f g → set_eq g f.
Proof.
  intros A B f g [Hfg Hgf]. split; intros i;
  [ destruct (Hgf i) | destruct (Hfg i) ];
  eexists; symmetry; eauto.
Qed.

Lemma set_eq_trans :
  ∀ {A B C} (f : A → surreal) (g : B → surreal) (h : C → surreal),
  set_eq f g → set_eq g h → set_eq f h.
Proof.
  intros A B C f g h [Hfg Hgf] [Hgh Hhg]. split; intros i.
  - destruct (Hfg i) as [j Hij].
    destruct (Hgh j) as [k Hjk].
    eexists; etransitivity; eauto.
  - destruct (Hhg i) as [j Hji].
    destruct (Hgf j) as [k Hkj].
    eexists; etransitivity; eauto.
Qed.

Lemma set_eq_union_comm :
  ∀ {A B} (f : A → surreal) (g : B → surreal),
  set_eq (f ∪ g) (g ∪ f).
Proof.
  split; intros [p | p].
  all: match goal with
  | p : ?T |- ∃ _ : ?T + _, _ => exists (inl p)
  | p : ?T |- ∃ _ : _ + ?T, _ => exists (inr p)
  end; unfold union; reflexivity.
Qed.

Lemma union_mor :
  ∀ {A B C D} (f : A → surreal) (g : B → surreal)
    (f' : C → surreal) (g' : D → surreal),
  set_eq f f' → set_eq g g' →
  set_eq (f ∪ g) (f' ∪ g').
Proof.
  intros A B C D f g f' g' [Hff' Hf'f] [Hgg' Hg'g].
  split; intros [i | i].
  all: match goal with
  | i : ?T, H : ∀ _ : ?T, _ |- _ =>
    destruct (H i) as [j Hj]
  end; match goal with
  | p : ?T |- ∃ _ : ?T + _, _ => exists (inl p)
  | p : ?T |- ∃ _ : _ + ?T, _ => exists (inr p)
  end; unfold union; auto.
Qed.

Definition eqs (x y : surreal) :=
  match x, y with
  | [lx, rx], [ly, ry] => set_eq lx ly ∧ set_eq rx ry
  end.

Infix "≡s" := eqs (at level 70).

Theorem eqs_refl : ∀ x : surreal, x ≡s x.
Proof.
  destruct x. split; apply set_eq_refl.
Qed.

Theorem eqs_sym : ∀ x y : surreal, x ≡s y → y ≡s x.
Proof.
  destruct x as [Lx Rx lx rx].
  destruct y as [Ly Ry ly ry].
  intros [Hlx Hrx]. split; apply set_eq_sym; assumption.
Qed.

Theorem eqs_trans : ∀ x y z : surreal,
  x ≡s y → y ≡s z → x ≡s z.
Proof.
  destruct x as [Lx Rx lx rx].
  destruct y as [Ly Ry ly ry].
  destruct z as [Lz Rz lz rz].
  intros [Hlx Hrx] [Hly Hry].
  split; eapply set_eq_trans; eauto.
Qed.

Add Relation surreal eqs
  reflexivity proved by eqs_refl
  symmetry proved by eqs_sym
  transitivity proved by eqs_trans as eqs_rel.

Theorem eqs_eq : ∀ x y : surreal, x ≡s y → x ≡ y.
Proof.
  intros [Lx Rx lx rx] [Ly Ry ly ry] [[Hlx Hly] [Hrx Hry]].
  do 2 split; intros p.
  all: match goal with
  | p : ?T, H : ∀ _ : ?T, _ |- _ =>
    destruct (H p) as [j Hj]
  end;
  solve_snge; eexists; apply Hj.
Qed.

Add Morphism seq with signature eqs ==> eqs ==> iff as seq_mor.
Proof.
  split; intros;
  [rewrite <- (eqs_eq x y H), <- (eqs_eq x0 y0 H0) |
   rewrite (eqs_eq x y H), (eqs_eq x0 y0 H0)]; auto.
Qed.

Hint Resolve eqs_eq : core.
