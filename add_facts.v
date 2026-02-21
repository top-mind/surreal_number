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
  do 2 split.
  all: intros [p|p]; [exists (inl p) | exists (inr p)]; cbn [union].
  all: try rewrite IH1; try rewrite IH2; try rewrite IH3; try rewrite IH4.
  all: try reflexivity.
Qed.

Theorem T18' : ∀ x y, (- (x + y)) ≡ (- x) + (- y).
Proof.
  split.
  all: apply sadd_sle_mono_l_rev with (z := x + y).
  all: rewrite (ssub_diag (x + y)).
  all: rewrite (sadd_comm (-x) (-y)).
  all: rewrite <-sadd_assoc.
  all: rewrite sadd_assoc with (x:=x).
  all: rewrite (ssub_diag y).
  all: rewrite sadd_zero.
  all: rewrite (ssub_diag x).
  all: reflexivity.
Qed.
