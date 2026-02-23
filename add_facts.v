From Stdlib Require Import Utf8_core.
From SN Require Import base equiv add.

Theorem T17 : ∀ x y, x + y - y ≡ x.
Proof.
  intros. unfold ssub.
  rewrite sadd_assoc.
  rewrite (ssub_diag y).
  apply sadd_zero.
Qed.

Theorem T18 : ∀ x y, (- (x + y)) ≡s (- x) + (- y).
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
