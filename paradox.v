From SN Require Import base equiv.

Theorem regularity_l : ∀ x : surreal, match x with
  | [l, r] => ∀ i, l i ≠ x
  end.
Proof.
  induction x as [L R l IHl r IHr].
  intros i H.
  specialize (IHl i).
  rewrite H in IHl.
  apply (IHl i H).
Qed.

Theorem regularity_l_eq : ∀ x : surreal, match x with
  | [l, r] => ∀ i, ~ l i ≡ x
  end.
Proof.
  intros [L R l r] i [_ H].
  eapply sle_not_snge. exact H.
  auto.
Qed.

Fail Definition X := [ λ x, x, ess ].

Unset Universe Checking.

Definition X := [ λ x, x, ∅ ].

Theorem X_not_seq : ∀ x, ~ x ≡ X.
Proof.
  exact (regularity_l_eq X).
Qed.

Theorem paradox : False.
Proof. apply X_not_seq with (x:=X). reflexivity. Qed.

(* Print Assumptions paradox. *)
(* Type hierarchy is collapsed (logic is inconsistent) *)