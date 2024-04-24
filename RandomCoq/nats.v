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


Fixpoint eqb (a b :nat) : bool :=
  match a, b with
  | O, O => true
  | O, _ => false
  | _, O => false
  | S n, S m => eqb n m
  end.


Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 40, left associativity) : nat_scope.

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


Theorem eqb_refl : ∀ n : nat, (n =? n) = true.
Proof.

  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem mult_0_plus' : ∀ n m : nat, (n + 0 + 0) * m =  n * m.
Proof.
  intros n m.
  assert ( H: n + 0 + 0 = n ).
  { rewrite plus_commutative. rewrite zero_identity_l. rewrite -> plus_commutative. rewrite zero_identity_l. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange_firsttry : ∀ n m p q : nat, (n + m)+ (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* rewrite -> plus_commutative. *) (* doesn't work. can prove a lemma with vars in scope {-# LANGUAGE ScopedTypeVariables #-} *)
  assert (H: n + m = m + n). { rewrite -> plus_commutative. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

 (* all of following to prove commutativity of * may be possible in fewer steps (maybe ~simpl.~ does more for you?) *)

Theorem mul_zero_l : ∀ x : nat, 0 * x = 0.
Proof.
  intros x.
  induction x as [|x' IHx'].
  - reflexivity.
  -  simpl. reflexivity.
Qed.

Theorem mul_zero_r : ∀ x : nat, x * 0 = 0.
Proof.
  intros x.
  induction x as [|x' IHx'].
  - reflexivity.
  - simpl. rewrite -> IHx'. reflexivity.
Qed.

(* following 2 Theorems may be shortened with ~Theorem add_shuffle3 : ∀ n m p : nat, n + (m + p) = m + (n + p).~ *)
Theorem comm_3 : ∀ x y z : nat, x + (y + z) = x + (z + y).
Proof.
  intros x y z.
  assert (G: y + z = z + y).
  { rewrite -> plus_commutative. reflexivity. }
  rewrite G.
  reflexivity.
Qed.

Theorem brace_dont_matter : ∀ x y z : nat, x + (y + z) = x + y + z.
Proof.
  intros x y z.
  induction x as [|x' IHx'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHx'. reflexivity.
Qed.

Theorem destributive_r : ∀ a b : nat, a * S b = a + a * b.
Proof.
  intros a b.
  induction a as [|a' IHa'].
  - rewrite -> mul_zero_l. rewrite -> mul_zero_l. simpl. reflexivity.
  - simpl. rewrite -> IHa'. rewrite -> plus_commutative. rewrite comm_3. rewrite -> brace_dont_matter. reflexivity.
Qed.

Theorem mul_comm : ∀ a b : nat, a * b = b * a.
Proof.
  intros a b.
  induction a as [|a' IHa'].
  - rewrite -> mul_zero_l. rewrite -> mul_zero_r. reflexivity.
  - simpl. rewrite ->IHa'.  rewrite -> destributive_r. reflexivity.
Qed.
