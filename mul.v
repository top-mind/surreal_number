From Stdlib Require Import FunctionalExtensionality.
From SN Require Import base equiv add.

Fixpoint smul (x : surreal) : surreal → surreal :=
  match x with
  | [lx, rx] =>
    fix smul_y (y : surreal) : surreal :=
      match y with
      | [ly, ry] =>
        [ uncurry (λ i j, smul (lx i) y + smul_y (ly j) - smul (lx i) (ly j)) ∪
          uncurry (λ i j, smul (rx i) y + smul_y (ry j) - smul (rx i) (ry j)),
          uncurry (λ i j, smul (lx i) y + smul_y (ry j) - smul (lx i) (ry j)) ∪
          uncurry (λ i j, smul (rx i) y + smul_y (ly j) - smul (rx i) (ly j)) ]
      end 
  end.

Infix "*" := smul : surreal_scope.

Theorem smul_rewrite : ∀ Lx Rx Ly Ry (lx : Lx → surreal) (rx : Rx → surreal)
  (ly : Ly → surreal) (ry : Ry → surreal),
  [lx, rx] * [ly, ry] =
  [ uncurry (λ i j, (lx i) * [ly, ry] + [lx, rx] * (ly j) - (lx i) * (ly j)) ∪
    uncurry (λ i j, (rx i) * [ly, ry] + [lx, rx] * (ry j) - (rx i) * (ry j)),
    uncurry (λ i j, (lx i) * [ly, ry] + [lx, rx] * (ry j) - (lx i) * (ry j)) ∪
    uncurry (λ i j, (rx i) * [ly, ry] + [lx, rx] * (ly j) - (rx i) * (ly j)) ].
Proof.
  reflexivity.
Qed.

Lemma ssub_sadd_swap_mor_eqs :
  ∀ a b a' b' c c',
  a ≡s a' → b ≡s b' → c ≡s c' →
  a + b - c ≡ b' + a' - c'.
Proof.
  intros.
  rewrite (sadd_comm a b).
  do 3 match goal with
  | H : _ ≡s _ |- _ => apply eqs_eq in H; rewrite H
  end.
  reflexivity.
Qed.

Theorem smul_comm_eqs : ∀ x y, x * y ≡s y * x.
Proof.
  intros x. induction x as [Lx Rx lx IHlx rx IHrx].
  intros y. induction y as [Ly Ry ly IHly ry IHry].
  rewrite !smul_rewrite. split.
  2: eapply set_eq_trans; [apply set_eq_union_comm |].
  all: apply union_mor; split; intros [i j]; exists (j, i);
    apply ssub_sadd_swap_mor_eqs; auto.
Qed.

Corollary smul_comm : ∀ x y, x * y ≡ y * x.
Proof. intros. apply eqs_eq. apply smul_comm_eqs. Qed.

Theorem smul_sadd_distr_l : ∀ x y z, x * (y + z) ≡ x * y + x * z.
Proof.
  intros [Lx Rx lx rx] [Ly Ry ly ry] [Lz Rz lz rz].
  rewrite sadd_rewrite.
  rewrite smul_rewrite.
Admitted.

Theorem smul_assoc_eqs : ∀ x y z, (x * y) * z ≡s x * (y * z).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  induction z as [Lz Rz lz IH5 rz IH6].
  rewrite !smul_rewrite.
  do 2 split.
  - intros [([(xᴸ,yᴸ)|(xᴿ,yᴿ)],zᴸ)|].
    exists (inl (xᴸ, inl (yᴸ, zᴸ))).
    do 6 (unfold uncurry at 1; cbn [union];
      try rewrite <- smul_rewrite).
Admitted.

(*
(lx xᴸ * [ly, ry] + [lx, rx] * ly yᴸ - lx xᴸ * ly yᴸ) * [lz, rz] + [lx, rx] * [ly, ry] * lz zᴸ -
(lx xᴸ * [ly, ry] + [lx, rx] * ly yᴸ - lx xᴸ * ly yᴸ) * lz zᴸ
≡ lx xᴸ * ([ly, ry] * [lz, rz]) + [lx, rx] * (ly yᴸ * [lz, rz] + [ly, ry] * lz zᴸ - ly yᴸ * lz zᴸ) -
lx xᴸ * (ly yᴸ * [lz, rz] + [ly, ry] * lz zᴸ - ly yᴸ * lz zᴸ)
*)