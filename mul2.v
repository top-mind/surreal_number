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

Example t_ast : 2 * ∗ ≡s [⟨∗⟩, ⟨∗⟩].
Proof.
  rewrite smul_rewrite. split; introall; try exists tt.
  2, 4: exists (inl (tt, tt)).
  all: cbn [union uncurry]; rewrite ?smul_0, ?sopp_0, ?sadd_0, smul_comm;
    apply smul_1.
Qed.

Example two_ast : two * ∗ ≡s [⟨0, ∗⟩, ⟨0, ∗⟩].
Proof with cbn [union uncurry]; rewrite !smul_0, sopp_0, !sadd_0, smul_comm; auto using smul_1.
  rewrite smul_rewrite. split; introall.
  1, 5: exists (inl tt)...
  1, 4: exists (inr tt)...
  1, 3: exists (inl (inl tt, tt))...
  1, 2: exists (inl (inr tt, tt))...
Qed.

From SN Require Import pseudo.

Lemma t_ast_two_ast : [⟨∗⟩, ⟨∗⟩] ≱ [⟨0, ∗⟩, ⟨0, ∗⟩].
Proof.
  rewrite zzzz_is_0.
  replace 0 with (⟨0, ∗⟩ (inl tt)) at 1 by auto.
  apply range_l with (lx:=⟨0, ∗⟩) (rx:=⟨0, ∗⟩).
Qed.

Example n0_p_neq0 : ∃ n p, num n ∧ n ≡ 0 ∧ ~ n * p ≡ 0.
Proof.
  exists (two - 2), ∗.
  split.
  - apply sadd_num; try apply num_two; apply num_m2.
  - split. rewrite two_is_2. apply ssub_diag.
    intro H.
    rewrite smul_sadd_distr_r, two_ast, smul_sopp_distr_l, t_ast in H.
    apply sadd_shift_item in H.
    destruct H. apply sle_not_snge in H.
    auto using t_ast_two_ast.
Qed.

Example n_p0_neq0 : ∃ p n, num n ∧ p ≡ 0 ∧ ~ n * p ≡ 0.
Admitted.

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