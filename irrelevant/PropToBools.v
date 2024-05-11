From Coq Require Import Unicode.Utf8.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb n' m'
  | _, _ => false
  end.


Theorem S_injective : ∀ (n m : nat),
    S n = S m → n = m.
Proof.
  intros.
  injection H.
  intros.
  apply H0.
Qed.

Theorem S_inject : ∀ (n m : nat),
    n = m → S n = S m.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Theorem eqb_eq : ∀ (n m : nat),
    eqb n m = true → n = m.
Proof.
  induction n.
  + intros. induction m. reflexivity. discriminate H.
  + intros. induction m. discriminate H. apply S_inject, IHn. simpl in H. apply H.
Qed.


Theorem same_is_same : ∀ (n : nat),
    eqb n n = true.
Proof.
  intros.
  induction n. reflexivity. simpl. rewrite IHn. reflexivity.
Qed.

Theorem eqb_iff_eq : ∀ (n m : nat),
    eqb n m = true ↔ n = m.
Proof.
  split.
  - apply eqb_eq.
  - induction n.
    + intros. rewrite <- H.  reflexivity.
    + intros. rewrite H. apply same_is_same.
Qed.
