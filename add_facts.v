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