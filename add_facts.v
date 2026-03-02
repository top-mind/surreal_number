From Stdlib Require Import Utf8_core.
From SN Require Import base equiv add.

(** T18 *)
Theorem sopp_sadd : ∀ x y, (- (x + y)) ≡s (- x) + (- y).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  rewrite sadd_rewrite.
  cbn [sopp].
  rewrite sadd_rewrite.
  split; intros [i|i];
    try exists (inl i);
    try exists (inr i);
    cbn [union]; auto.
Qed.

Theorem sadd_shift_item : ∀ x y, x - y ≡ 0 → x ≡ y.
Proof.
  intros.
  rewrite <- sadd_ssub_id with (y:=y).
  rewrite sadd_comm with (x:=x), sadd_assoc, H. auto.
Qed.

Ltac introall :=
  repeat match goal with
  | |- forall _ : _, _ => intros ?i
  | h : _ * _ |- _ => destruct h as [?i ?j]
  | h : _ + _ |- _ => destruct h as [?h | ?h]
  | h : Empty_set |- _ => destruct h
  end.

Notation "⟨ x ⟩" := (singleton x) : surreal_scope.

Notation "⟨ x , y , .. , z ⟩" :=
(union .. (union (singleton x) (singleton y)) .. (singleton z)) : surreal_scope.

From Stdlib Require Import FunctionalExtensionality.

Notation "2" := [⟨1⟩, ∅].

Lemma num_2 : num 2.
Proof. repeat split; introall. Qed.

Lemma sopp_2 : (-2) = [∅, ⟨(-1)⟩].
  rewrite sopp_rewrite. f_equal.
  extensionality i. tauto.
Qed.

Lemma num_m2 : num (-2).
Proof. repeat split; introall. Qed.

Example opo : 1 + 1 ≡s 2.
Proof.
  rewrite sadd_rewrite.
  split; introall; try exists tt; try exists (inr tt); cbn [union];
    unfold singleton; [rewrite sadd_comm| |]; auto.
Qed.

Notation mo_o := [⟨(-1)⟩, ⟨1⟩].

Example omo : 1 - 1 ≡s mo_o.
Proof.
  rewrite sopp_1, sadd_rewrite.
  split; introall; destruct i;
    try exists tt; try exists (inr tt); try exists (inl tt);
    cbn [union];
    unfold singleton.
    1, 2: rewrite sadd_comm. all: auto.
Qed.

Notation two := [⟨0, 1⟩, ∅].

Lemma two_is_2 : two ≡ 2.
Proof.
  repeat split; introall.
  - constructor. left. exists tt. apply cmp_m1_0_1.
  - constructor. left. exists tt. reflexivity.
  - left. exists (inr tt). reflexivity.
Qed.

Lemma num_two : num two.
Proof. repeat split; introall; apply num_0_1_m1. Qed.

Notation m1_mo_o__t := [⟨(-1), mo_o⟩, ⟨two⟩].

Theorem t_m1 : two - 1 ≡s m1_mo_o__t.
  rewrite sopp_1, sadd_rewrite.
  split; introall.
  - exists (inl tt). cbn [union].
    rewrite sadd_comm. auto.
  - exists (inr tt). cbn [union].
    rewrite <- sopp_1, omo. reflexivity.
  - exists (inl (inl tt)). cbn [union].
    rewrite sadd_comm. auto.
  - exists (inl (inr tt)). cbn [union].
    rewrite <- sopp_1, omo. reflexivity.
  - exists tt. cbn [union]. auto.
  - exists (inr tt). cbn [union]. auto.
Qed.

Notation mt__mo_o := [⟨(-2)⟩, ⟨mo_o⟩].

Theorem mo_o_m1 : mo_o - 1 ≡s mt__mo_o.
  rewrite sopp_1, sadd_rewrite.
  split; introall; try exists tt.
  - cbn [union].
    rewrite <- sopp_1.
    unfold singleton. rewrite <- sopp_sadd, opo.
    reflexivity.
  - exists (inl tt). cbn [union].
    rewrite <- sopp_1.
    unfold singleton. rewrite <- sopp_sadd, opo.
    reflexivity.
  - cbn [union]. rewrite <- sopp_1, omo. reflexivity.
  - cbn [union]. auto.
  - exists (inr tt). cbn [union]. auto.
Qed.

Goal m1_mo_o__t - 1 ≡s [⟨(-2), mt__mo_o⟩, ⟨m1_mo_o__t⟩].
  rewrite sopp_1, sadd_rewrite.
  split; introall; try exists tt.
  - exists (inl tt). cbn [union].
    rewrite <- sopp_1. unfold singleton.
    rewrite <- sopp_sadd, opo. reflexivity.
  - exists (inr tt). cbn [union].
    rewrite <- sopp_1, mo_o_m1. reflexivity.
  - exists (inl (inl tt)). cbn [union].
    rewrite <- sopp_1. unfold singleton.
    rewrite <- sopp_sadd, opo. reflexivity.
  - exists (inl (inr tt)). cbn [union].
    rewrite <- sopp_1, mo_o_m1. reflexivity.
  - cbn [union]. rewrite <- sopp_1. apply t_m1.
  - cbn [union]. auto.
  - exists (inr tt). cbn [union]. auto.
Qed.