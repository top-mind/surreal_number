From Stdlib Require Import Classical.
From SN Require Import base.

(**
After Chapter 5. Assume that g is a funcion from numbers to numbers such that x ≤ y implies g(x) ≤ g(y).
Define f(x) = (f(xL) ∪ {g(x)}, f(xR)).
Prove that f(x) ≤ f(y) if and only if x ≤ y.
*)

Module Exercise2.
  Parameter g : surreal → surreal.
  Parameter g_monotone : ∀ x y, x ≤ y → g x ≤ g y.

  Fixpoint f (x : surreal) : surreal :=
    match x with
    | snlr L R l r => [ λ i, match i with
                                 | inl li => f (l li)
                                 | inr tt => g x
                                 end,
                         λ j, f (r j) ]
    end.

  (* Eval simpl in f (zero). *) (* f(0) = (g(0),) *)
  (* Eval simpl in f (one). *) (* f(1) = ((g(0),) g(1),) *)
  (* Eval simpl in f (neg_one). *) (* f(-1) = (g(-1), (g(0), )) *)

  Lemma aux : ∀ x y, (x ≤ y → f x ≤ f y) ∧ (x ≱ y → f x ≱ f y).
  Proof with eauto; try apply range.
    induction x as [Lx Rx lx IH1 rx IH2].
    induction y as [Ly Ry ly IH3 ry IH4].
    split; intros H.
    - simpl. constructor; intros.
      + destruct i as [i | []].
        * apply IH1 with (l:=i) (y:=[ly, ry]).
          eapply trans2...
        * solve_snge.
          exists (inr tt). apply g_monotone. apply H.
      + apply IH4 with (r:=j).
        eapply trans...
    - sinv H; simpl; constructor.
      + left. exists (inl i). apply IH3...
      + right. exists j.
        apply IH2 with (y:=[ly, ry])...
  Qed.

  Theorem f_le_f_iff : ∀ x y, f x ≤ f y ↔ x ≤ y.
  Proof.
    intros x y. split.
    - intros. apply not_snge_sle. intros H0.
      apply aux in H0. apply sle_not_snge in H. contradiction.
    - apply aux.
  Qed.
End Exercise2.

From SN Require Import equiv.
From Stdlib Require Import Setoid.

Module Exercise3.
  (* Merged into equiv.v *)
End Exercise3.

From SN Require Import add.

Module Exercise7.
  (* add.v: sopp_mor *)
End Exercise7.

Module Exercise8.
  (* TODO *)
End Exercise8.

Module Exercise9.
  (* TODO *)
End Exercise9.

Module Exercise10.
  (* Done in add.v *)
End Exercise10.

Module Exercise15.
  (* Done in paradox.v *)
End Exercise15.