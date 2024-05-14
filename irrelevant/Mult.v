From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.

Axiom plus_assoc : ∀ n m o : nat, (n + m) + o = n + (m + o).
Axiom plus_comm : ∀ n m : nat, n + m = m + n.
Axiom mult_comm : ∀ n m : nat, n * m = m * n.
Theorem functions: ∀ (A B : Type) (f : A → B) (x y : A),
    x = y → f x = f y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

    
Theorem check_def_mult : ∀ n m : nat,
    S n * m = m + n * m.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem mult_plus_ring : ∀ n m o: nat,
    n * (m + o) = n * m + n * o.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. rewrite <- (plus_assoc (m + o) (n * m) (n * o)).
    rewrite <- (plus_assoc (m + n * m) o (n * o)).
    rewrite (plus_comm (m + o + n * m) (n * o)).
    rewrite (plus_comm (m + n * m + o) (n * o)).
    apply (functions _ _ (plus (mult n o))).
    rewrite plus_assoc.
    rewrite plus_assoc.
    apply (functions _ _ (plus m)), plus_comm.
Qed.


Theorem mult_assoc : ∀ n m o : nat,
    (n * m) * o = n * (m * o).
Proof.
  induction n.
  - reflexivity.
  - intros. simpl. rewrite mult_comm.
    rewrite <- IHn.
    rewrite mult_plus_ring.
    rewrite mult_comm.
    rewrite (plus_comm (m * o) ).
    rewrite (plus_comm (m * o) ).
    rewrite (mult_comm o (n * m)).
    reflexivity.
Qed.
    
