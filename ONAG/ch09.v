From SN Require Import ONAG.game.

Inductive state : Game → bool → bool → Prop :=
| left_win : ∀ L R (l : L → Game) (r : R → Game),
    (∃ i, state (l i) false false) →
    state [l, r] true true
| right_win : ∀ L R (l : L → Game) (r : R → Game),
    (∃ j, state (r j) true false) →
    state [l, r] false true
| left_lose : ∀ L R (l : L → Game) (r : R → Game),
    (∀ i, state (l i) false true) →
    state [l, r] true false
| right_lose : ∀ L R (l : L → Game) (r : R → Game),
    (∀ j, state (r j) true true) →
    state [l, r] false false.

Theorem state_not_and : ∀ G, (state G true true → ~ state G true false) ∧ (state G false true → ~ state G false false).
Proof.
  induction G as [L R l IHl r IHr].
  split; intros H1 H2; eqdep_inv H1; eqdep_inv H2; destruct H0 as [i H0].
  - destruct (IHl i) as [_ ?].
    intuition.
  - destruct (IHr i) as [? _].
    intuition.
Qed.

From Stdlib Require Import Classical.

Theorem state_dec : ∀ G, (state G true true ∨ state G true false) ∧ (state G false true ∨ state G false false).
Proof.
  induction G as [L R l IHl r IHr].
  split.
  - destruct (classic (∃ i, state (l i) false false)).
    + left. constructor. assumption.
    + right. constructor. intros i.
      apply not_ex_all_not with (n := i) in H. 
      destruct (IHl i) as [_ []]; auto; contradiction.
  - destruct (classic (∃ j, state (r j) true false)).
    + left. constructor. assumption.
    + right. constructor. intros j.
      apply not_ex_all_not with (n := j) in H.
      destruct (IHr j) as [[] _]; auto; contradiction.
Qed.

Definition G_gt_0 := λ G, state G true true ∧ state G false false.
Definition G_lt_0 := λ G, state G false true ∧ state G true false.
Definition G_eq_0 := λ G, state G true false ∧ state G false false.
Definition G_par_0 := λ G, state G true true ∧ state G false true.

Definition G_ge_0 := λ G, G_gt_0 G ∨ G_eq_0 G.
Definition G_le_0 := λ G, G_lt_0 G ∨ G_eq_0 G.

(** G ⊳ 0 *)
Definition G_tr_0 := λ G, G_gt_0 G ∨ G_par_0 G.
(** G ⊲ 0 *)
Definition G_tl_0 := λ G, G_lt_0 G ∨ G_par_0 G.

Theorem G_ge_0_iff : ∀ G, G_ge_0 G ↔ state G false false.
Proof.
  split; intros.
  - destruct H; apply H.
  - unfold G_ge_0, G_gt_0, G_eq_0.
    destruct (state_dec G) as ([H1|H1],_); [left|right]; auto.
Qed.

Theorem G_le_0_iff : ∀ G, G_le_0 G ↔ state G true false.
Proof.
  split; intros.
  - destruct H; apply H.
  - unfold G_le_0, G_lt_0, G_eq_0.
    destruct (state_dec G) as (_,[H1|H1]); [left|right]; auto.
Qed.

Theorem G_tr_0_iff : ∀ G, G_tr_0 G ↔ state G true true.
Proof.
  split; intros.
  - destruct H; apply H.
  - unfold G_tr_0, G_gt_0, G_par_0.
    destruct (state_dec G) as (_,[H1|H1]); [right|left]; auto.
Qed.

Theorem G_tl_0_iff : ∀ G, G_tl_0 G ↔ state G false true.
Proof.
  split; intros.
  - destruct H; apply H.
  - unfold G_tl_0, G_lt_0, G_par_0.
    destruct (state_dec G) as ([H1|H1],_); [right|left]; auto.
Qed.

(** THEOREM 50. Each game G belongs to on of the outcome classes above. *)

From SN Require Import add.

Theorem state_neg : ∀ G b, (state G true b ↔ state (-G) false b) ∧ (state G false b ↔ state (-G) true b).
Proof.
  induction G as [L R l IHl r IHr].
  do 2 split; intros H; eqdep_inv H; simpl; constructor.
  all: try (destruct H5 as [i]; exists i).
  all: try intros.
  all: try apply IHl; try apply IHr; auto.
Qed.
