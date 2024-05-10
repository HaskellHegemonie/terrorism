(* examples from: https://www.youtube.com/watch?v=VxINoKFm-S4 *)
From Coq Require Import Unicode.Utf8.
From Coq Require Import List.
From Coq Require Import Nat.
From Coq Require Import Bool.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Fixpoint half (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n) => S (half n)
  end.

Compute half 5.
Definition even (n : nat) : Prop := ∃ m : nat, double (half m) = n.


Theorem zero_even : even O.
Proof.
  unfold even.
  exists O.
  reflexivity.
Qed.

Definition odd (n : nat) : Prop := ∃ m : nat, S (double (half m)) = n.

Theorem one_odd : odd 1.
Proof.
  unfold odd.
  exists 1.
  reflexivity.
Qed.

Theorem add1_even_odd : ∀ n : nat,
    even n → odd (S n).
Proof.
  intros n.
  unfold even.
  intros [m H].
  unfold odd.
  exists m.
  rewrite H.
  reflexivity.
Qed.

Theorem even_or_odd : ∀ n : nat,
    even n ∨ odd n.
Proof.
  intros n.
  induction n as [| n' [[meven IHeven] | [modd IHodd]] ].
  - left. apply zero_even.
  - right. apply add1_even_odd. unfold even. exists meven. apply IHeven.
  - left. unfold even. exists (2 + modd). rewrite <- IHodd. reflexivity.
Qed.
