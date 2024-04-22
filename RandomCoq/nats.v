From Coq Require Import Unicode.Utf8.

Fixpoint plus (a b : nat) : nat :=
  match a with
  | O => b
  | S n => S (plus n b)
  end.

Fixpoint mult (a b : nat) : nat :=
  match a with
  | O => O
  | S n => plus b (mult n b)
  end.

(* Compute mult 8 3 = 24. *)
Example mult_8_3_eq_24: mult 8 3 = 24.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (a b : nat) : nat :=
  match a,b with
  | _, O => a
  | O, _ => O
  | S n, S m => minus n m
  end.

Compute minus 8 3.

Fixpoint exp (a b : nat) : nat :=
  match b with
  | O => 1
  | S n => mult a (exp a n)
  end.

Compute exp 2 8.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Theorem a: ∀ a b : nat, a = b → a + a = b + b.
Proof.
  intros a b aEqB.
  rewrite -> aEqB.
  reflexivity.
Qed.

Theorem andb_commutative : ∀ a b : bool, andb a b = andb b a.
Proof.
  { intros [] [].
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
  }
Qed.

Theorem andb_commutative' : ∀ a b : bool, andb a b = andb b a.
Proof.
  (* this somehow works *)
  intros [] []; reflexivity.
Qed.


Theorem andb_true_elim2: ∀ a b : bool, andb a b = true -> b = true.
Proof.
  (*   intros [] []  aNbTrue. *)
  (*   - reflexivity. *)
  (*   - inversion aNbTrue. *)
  (*   - reflexivity. *)
  (*   - inversion aNbTrue. *)
  (* or better: *)
  intros [] [] H; inversion H; reflexivity.
Qed.
