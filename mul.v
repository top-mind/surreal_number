From Stdlib Require Import FunctionalExtensionality.
From SN Require Import base equiv add add_facts.

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

Theorem smul_comm_eqs : ∀ x y, x * y ≡s y * x.
Proof.
  intros x. induction x as [Lx Rx lx IH1 rx IH2].
  intros y. induction y as [Ly Ry ly IH3 ry IH4].
  rewrite !smul_rewrite. split;
  intros [(i,j)|(i,j)];
  try exists (inl (j,i));
  try exists (inr (j,i)); cbn [union uncurry];
  apply ssub_mor_eqs; auto;
  rewrite sadd_comm_eqs; apply sadd_mor_eqs; auto.
Qed.

Corollary smul_comm : ∀ x y, x * y ≡ y * x.
Proof. intros. apply eqs_eq. apply smul_comm_eqs. Qed.

Lemma smul_sadd_distr_aux : ∀ a b c d e,
  a + b + (c + d) - (e + b) ≡ a + c - e + d ∧
  a + b + (c + d) - (a + e) ≡ c + (b + d - e).
Proof. split; unfold ssub; rewrite sopp_sadd.
  - rewrite sadd_comm, <-!sadd_assoc. solve_sadd.
    rewrite 3 sadd_assoc, sadd_comm. solve_sadd.
    rewrite <-!sadd_assoc. solve_sadd.
    rewrite sadd_comm, <-sadd_assoc, (ssub_diag b).
    rewrite sadd_comm. apply sadd_zero.
  - rewrite <-!sadd_assoc. solve_sadd.
    rewrite sadd_comm, <-!sadd_assoc. solve_sadd.
    rewrite sadd_comm. solve_sadd.
    rewrite sadd_comm. rewrite <-(sadd_zero b) at 2. solve_sadd.
    rewrite sadd_comm. apply ssub_diag.
Qed.

Theorem smul_sadd_distr_l : ∀ x y z, x * (y + z) ≡ x * y + x * z.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  induction z as [Lz Rz lz IH5 rz IH6].
  rewrite sadd_rewrite, !smul_rewrite, <- !sadd_rewrite.
  match goal with
  | |- _ ≡ ?tm => remember tm as t; rewrite sadd_rewrite in Heqt; subst
  end; rewrite <- !smul_rewrite.
  apply set_eq_seq; split;
    try intros [(i,[j|j])|(i,[j|j])];
    try intros [[(i,j)|(i,j)]|[(i,j)|(i,j)]];
    try exists (inl (inl (i,j)));
    try exists (inl (inr (i,j)));
    try exists (inr (inl (i,j)));
    try exists (inr (inr (i,j)));
    try exists (inl (i, inl j));
    try exists (inl (i, inr j));
    try exists (inr (i, inl j));
    try exists (inr (i, inr j));
  cbn [union uncurry]; rewrite ?IH1, ?IH2, ?IH3, ?IH4, ?IH5, ?IH6.
  all: try apply smul_sadd_distr_aux.
Qed.

Corollary smul_sadd_distr_r : ∀ x y z, (x + y) * z ≡ x * z + y * z.
Proof. intros. rewrite smul_comm, smul_sadd_distr_l. apply sadd_mor; apply smul_comm. Qed.

Theorem smul_sopp_distr_l : ∀ x y, (-x) * y ≡ (- x * y).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  rewrite sopp_rewrite, !smul_rewrite, sopp_rewrite.
  apply set_eq_seq; split;
  intros [(i,j)|(i,j)]; try exists (inl (i,j)); try exists (inr (i,j));
    cbn [union uncurry]; rewrite <- sopp_rewrite;
    rewrite ?IH1, ?IH2, ?IH3, ?IH4;
    unfold ssub; rewrite 2 sopp_sadd; reflexivity.
Qed.

Corollary smul_sopp_distr_r : ∀ x y, x * (-y) ≡ (-x * y).
Proof. intros. rewrite smul_comm, smul_sopp_distr_l, smul_comm. reflexivity. Qed.

Lemma smul_assoc_eqs_aux : ∀ a b c d e f g, a + b + c + d + (e + f + g) ≡ a + (b + d + f) + (c + e + g).
Proof.
  intros.
  rewrite !sadd_assoc. do 2 solve_sadd.
  rewrite sadd_comm, !sadd_assoc. solve_sadd.
  rewrite sadd_comm, !sadd_assoc. solve_sadd.
  rewrite sadd_comm, !sadd_assoc. solve_sadd.
Qed.

Theorem smul_assoc_eqs : ∀ x y z, (x * y) * z ≡ x * (y * z).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  induction z as [Lz Rz lz IH5 rz IH6].
  rewrite !smul_rewrite.
  apply set_eq_seq; split;
  try intros [([(i,j)|(i,j)],k)|([(i,j)|(i,j)],k)];
  try intros [(i,[(j,k)|(j,k)])|(i,[(j,k)|(j,k)])];
  try exists (inl (i, inl (j,k)));
  try exists (inr (i, inr (j, k)));
  try exists (inl (i, inr (j, k)));
  try exists (inr (i, inl (j, k)));
  try exists (inl (inl (i, j), k));
  try exists (inr (inl (i, j), k));
  try exists (inr (inr (i, j), k));
  try exists (inl (inr (i, j), k));
      cbn [union uncurry];
      rewrite <- !smul_rewrite;
      unfold ssub;
      rewrite !smul_sadd_distr_l, !smul_sadd_distr_r;
      rewrite !smul_sopp_distr_l, !smul_sopp_distr_r;
      rewrite !sopp_sadd;
      rewrite ?IH1, ?IH2, ?IH3, ?IH4, ?IH5, ?IH6.
  all: apply smul_assoc_eqs_aux.
Qed.
