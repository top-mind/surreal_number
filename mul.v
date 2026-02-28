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

Ltac introall :=
  repeat match goal with
  | |- forall _ : _, _ => intros ?i
  | h : _ * _ |- _ => destruct h as [?i ?j]
  | h : _ + _ |- _ => destruct h as [?h | ?h]
  end.

Theorem smul_zero : ∀ x, x * 0 ≡s 0.
Proof.
  intros [Lx Rx lx rx]. rewrite smul_rewrite. split;
    try (intros []); introall; destruct j.
Qed.

Theorem smul_comm : ∀ x y, x * y ≡s y * x.
Proof.
  intros x. induction x as [Lx Rx lx IH1 rx IH2].
  intros y. induction y as [Ly Ry ly IH3 ry IH4].
  rewrite !smul_rewrite. split;
  introall;
  try exists (inl (j,i));
  try exists (inr (j,i)); cbn [union uncurry];
  apply sadd_mor_eqs;
  rewrite ?IH1, ?IH2, ?IH3, ?IH4; try rewrite sadd_comm;
  reflexivity.
Qed.

Hint Resolve smul_zero smul_comm : core.

Lemma smul_sadd_distr_aux : ∀ a b c d e,
  a + b + (c + d) - (e + b) ≡ a + c - e + d ∧
  a + b + (c + d) - (a + e) ≡ c + (b + d - e).
Proof. 
  Local Ltac solve_sadd_perm_l :=
    rewrite sadd_comm, <- !sadd_assoc; solve_sadd.
  split; rewrite sopp_sadd.
  - solve_sadd_perm_l.
    rewrite 3 sadd_assoc, sadd_comm; solve_sadd.
    rewrite <-!sadd_assoc; solve_sadd.
    rewrite sadd_comm, <-!sadd_assoc, (ssub_diag b), sadd_comm; auto.
  - rewrite <-!sadd_assoc; solve_sadd.
    do 2 solve_sadd_perm_l.
    rewrite sadd_assoc; rewrite <-(sadd_zero c) at 2. solve_sadd.
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
  apply set_eq_seq; split; introall;
    try exists (inl (inl (i,j)));
    try exists (inl (inr (i,j)));
    try exists (inr (inl (i,j)));
    try exists (inr (inr (i,j)));
    try exists (inl (i, inl j));
    try exists (inl (i, inr j));
    try exists (inr (i, inl j));
    try exists (inr (i, inr j));
  cbn [union uncurry]; rewrite ?IH1, ?IH2, ?IH3, ?IH4, ?IH5, ?IH6; apply smul_sadd_distr_aux.
Qed.

Corollary smul_sadd_distr_r : ∀ x y z, (x + y) * z ≡ x * z + y * z.
Proof. intros. rewrite smul_comm, smul_sadd_distr_l. apply sadd_mor; auto. Qed.

Theorem smul_sopp_distr_l : ∀ x y, (-x) * y ≡ (- x * y).
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  induction y as [Ly Ry ly IH3 ry IH4].
  rewrite sopp_rewrite, !smul_rewrite, sopp_rewrite.
  apply set_eq_seq; split;
  intros [(i,j)|(i,j)]; try exists (inl (i,j)); try exists (inr (i,j));
    cbn [union uncurry]; rewrite <- sopp_rewrite;
    rewrite ?IH1, ?IH2, ?IH3, ?IH4;
    rewrite 2 sopp_sadd; reflexivity.
Qed.

Corollary smul_sopp_distr_r : ∀ x y, x * (-y) ≡ (-x * y).
Proof. intros. rewrite smul_comm, smul_sopp_distr_l, smul_comm. reflexivity. Qed.

Theorem smul_1 : ∀ x, x * 1 ≡s x.
Proof.
  induction x as [Lx Rx lx IH1 rx IH2].
  rewrite smul_rewrite.
  split; introall; try destruct j;
  try exists i;
  try exists (inl (i, tt));
  try exists (inr (i, tt));
  cbn [union uncurry];
  rewrite ?IH1, ?IH2, !smul_zero, sopp_zero, !sadd_zero;
  reflexivity.
Qed.


Lemma smul_assoc_aux : ∀ a b c d e f g, a + b + c + d + (e + f + g) ≡ a + (b + d + f) + (c + e + g).
Proof.
  Local Ltac solve_sadd_perm_r :=
    rewrite sadd_comm, !sadd_assoc; solve_sadd.
  intros.
  rewrite !sadd_assoc. do 2 solve_sadd.
  do 3 solve_sadd_perm_r.
Qed.

Theorem smul_assoc : ∀ x y z, (x * y) * z ≡ x * (y * z).
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
      rewrite !smul_sadd_distr_l, !smul_sadd_distr_r;
      rewrite !smul_sopp_distr_l, !smul_sopp_distr_r;
      rewrite !sopp_sadd;
      rewrite ?IH1, ?IH2, ?IH3, ?IH4, ?IH5, ?IH6.
  all: apply smul_assoc_aux.
Qed.
