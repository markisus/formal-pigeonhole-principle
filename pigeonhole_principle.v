Require Import Coq.Lists.List.
Import ListNotations.

Search lt.
Require Import Coq.Arith.PeanoNat.
Import Nat.

Require Import Omega.

Fixpoint sum_entries (l : @list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => x + (sum_entries l')
  end.

Lemma partition_nats :
  forall m n : nat,
    (n < m) \/ (m <= n).
Proof.
  intros n m.
  generalize dependent m.
  induction n; intros m.
  - right.
    apply le_0_n.
  - assert (H := IHn m).
    destruct H as [H | H].
    + left.
      apply lt_trans with n.
      apply H.
      apply lt_succ_diag_r.
    + destruct m.
      ++ left.
         apply lt_0_succ.
      ++ inversion H; subst.
         +++ left. repeat apply lt_succ_diag_r.
         +++ right.
             rewrite <- succ_le_mono. apply H1.
Qed.

Theorem pigeon_hole_principle :
  forall (l : @list nat),
    length l < sum_entries l ->
    exists x, In x l /\ x > 1.
Proof.
  induction l.
  intro H.
  - simpl in H.
    inversion H.
  - intros.
    simpl in H.
    assert (partition_2 := partition_nats 2 a).
    destruct partition_2.
    (* a < 2, use the induction hypothesis *)
    + assert (length l < sum_entries l).
      { omega. }
      apply IHl in H1.
      repeat destruct H1.
      exists x.
      simpl. split. right. assumption. assumption.
    (* a >= 2 use a *)
    + exists a.
      split.
      simpl. left. reflexivity.
      omega.
Qed.
