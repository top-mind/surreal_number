From SN Require Import base equiv add add_facts mul.
From Stdlib Require Import Setoid.

Theorem smul_eqs_r : ∀ x y z, y ≡s z → x * y ≡s x * z.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  intros [Lz Rz lz rz].
  intros. pose proof H. eqdep_inv H.
  rewrite !smul_rewrite.
  split; introall; ex_eq j;
    try exists (inl (i, j0));
    try exists (inr (i, j0));
    cbn [union uncurry];
    repeat apply sadd_mor_eqs; try apply sopp_mor_eqs; auto.
Qed.

Add Morphism smul with signature eqs ==> eqs ==> eqs as smul_mor_eqs.
Proof with auto using smul_eqs_r.
  intros. transitivity (x * y0)...
  rewrite (smul_comm y y0), smul_comm...
Qed.

Notation "∗" := [singleton 0, singleton 0].

Goal ∗ * ∗ ≡s ∗.
  rewrite smul_rewrite. split; introall;
    try exists tt; try exists (inl (tt, tt));
    cbn [union uncurry]; unfold singleton;
    rewrite smul_comm, !smul_zero, sopp_zero, !sadd_zero;
    reflexivity.
Qed.

(** THEOREM 8
  If [x] and [y] are numbers,
  (i) so is [x * y]
  (ii) [forall x₁ ≡ x₂, x₁ * y ≡ x₂ * y]
  (iii) [forall x₁ ≤ x₂ and y₁ ≤ y₂, x₁ * y₂ + x₂ * y₁ ≤ x₁ * y₁ + x₂ * y₂]
*)

Local Definition P1 x₁ x₂ y₁ y₂ :=
  x₁ ≤ x₂ → y₁ ≤ y₂ → x₁ * y₂ + x₂ * y₁ ≤ x₁ * y₁ + x₂ * y₂.

Local Definition P2 x₁ x₂ y₁ y₂ :=
  x₁ ≱ x₂ → y₁ ≱ y₂ → x₁ * y₂ + x₂ * y₁ ≱ x₁ * y₁ + x₂ * y₂.

Theorem smul_mono : ∀ x₁ x₂ y₁ y₂,
  P1 x₁ x₂ y₁ y₂ ∧ P2 x₁ x₂ y₁ y₂.
Proof with clear.
  unfold P1, P2.
  intros [Lx₁ Rx₁ lx₁ rx₁] [Lx₂ Rx₂ lx₂ rx₂] [Ly₁ Ry₁ ly₁ ry₁] [Ly₂ Ry₂ ly₂ ry₂].
  split; intros.
  - rewrite !smul_rewrite, !sadd_rewrite.
    do 4 rewrite <- smul_rewrite. split.
    + introall.
      * cbn [union uncurry].
        solve_snge.
        (** find an lx₂ > lx₁ *)
Admitted.

Goal ∀ x y, num x → num y → num (x * y).
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  intros H1 H2; inversion H1 as [? []]; inversion H2 as [? []].
  rewrite smul_rewrite; repeat split.
  - introall;
    cbn [union uncurry];
    repeat apply sadd_num; try apply sopp_num; auto.
  - introall;
    cbn [union uncurry];
    repeat apply sadd_num; try apply sopp_num; auto.
  - introall;
    cbn [union uncurry].

Admitted.