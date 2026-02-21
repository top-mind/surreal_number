From Stdlib Require Import FunctionalExtensionality.
From SN Require Import base equiv add.

Fixpoint smul (x y : surreal) {struct x} : surreal :=
  match x with
  | [lx, rx] =>
    let fix smul' y :=
      match y with
      | [ly, ry] =>
        [ uncurry (λ i j, smul (lx i) y + smul' (ly j) - smul (lx i) (ly j)) ∪
          uncurry (λ i j, smul (rx i) y + smul' (ly j) - smul (rx i) (ly j)),
          uncurry (λ i j, smul (lx i) y + smul' (ry j) - smul (lx i) (ry j)) ∪
          uncurry (λ i j, smul (rx i) y + smul' (ly j) - smul (rx i) (ly j)) ]
      end in
    smul' y
  end.

Infix "*" := smul : surreal_scope.

Theorem smul_equation : ∀ x y,
  x * y =
    match x, y with
    | [lx, rx], [ly, ry] =>
      [ uncurry (λ i j, (lx i) * y + x * (ly j) - (lx i) * (ly j)) ∪
        uncurry (λ i j, (rx i) * y + x * (ly j) - (rx i) * (ly j)),
        uncurry (λ i j, (lx i) * y + x * (ry j) - (lx i) * (ry j)) ∪
        uncurry (λ i j, (rx i) * y + x * (ly j) - (rx i) * (ly j)) ]
    end.
Proof.
  destruct x as [Lx Rx lx rx].
  destruct y as [Ly Ry ly ry].
  cbn [smul]; unfold union.
  f_equal; apply functional_extensionality; intros [|].
  all: match goal with
  | |- _ ?tm = _ => destruct tm
  end; cbn [smul]; reflexivity.
Qed.