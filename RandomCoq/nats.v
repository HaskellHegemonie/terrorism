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


Theorem zero_identity_l : ∀ a : nat, 0 + a = a.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem zero_identity_r : ∀ a : nat, a + 0 = a.
Proof.
  intros a.
  induction a as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem someth0 : ∀ a b : nat, S a + b = S (a + b).
Proof.
  intros ab.
  reflexivity.
Qed.

Theorem someth1 : ∀ a b : nat, a + S b = S (a + b).
Proof.
  intros a b.
  induction a as [|n' IHn'].
  - rewrite -> zero_identity_l. rewrite -> zero_identity_l. reflexivity.
  - rewrite -> someth0. rewrite -> someth0. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_commutative : ∀ a b : nat, a + b = b + a.
Proof.
  intros a b.
  induction a as [| n' IHn'].
  - rewrite -> zero_identity_l. rewrite -> zero_identity_r. reflexivity.
  - simpl. rewrite -> someth1. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_associative : ∀ a b c : nat, (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a as [|n' IHn'].
  - rewrite -> zero_identity_l. rewrite -> zero_identity_l. reflexivity.
    (* - rewrite -> someth0. rewrite -> someth0. rewrite -> someth0. rewrite -> IHn'. reflexivity. *)
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

