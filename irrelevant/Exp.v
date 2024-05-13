From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.

Fixpoint exp (n m : nat) : nat :=
  match m with
  | O => 1
  | S m' => mult n (exp n m')
  end.


Axiom ax0 : ∀ m : nat, m * 1 = m.
Axiom ax1 : ∀ n m a : nat, exp n m * exp n a = exp n (m + a). (* proven through ex1 *)
Axiom ax2 : ∀ n m o: nat, (n * m) * o = n * (m * o).

Theorem ex1 : ∀ n m a : nat, exp n m * exp n a = exp n (m + a).
Proof.
  induction m.
  - intros. simpl. rewrite <- plus_n_O. reflexivity.
  - intros. simpl. rewrite <- IHm. rewrite ax2. reflexivity.
Qed.

Theorem ex0 : ∀ (a n m : nat),
    exp (exp n m) a  = exp n (a * m).
Proof.
  induction a.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite -> IHa.  rewrite ex1. reflexivity.
Qed.
