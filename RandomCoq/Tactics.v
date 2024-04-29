(* tactics: apply, apply with, transitivity, injection, discriminate, `in`, specialize *)
From Coq Require Import Unicode.Utf8.
From LF Require Export Poly.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Import PeanoNat.
Theorem silly : ∀ (n m : nat), n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 : ∀ (n m o p : nat),
    n = m →
    (n = m → [n; o] = [m; p]) →
    [n; o] = [m; p].
Proof.
  intros n m o p eq0 eq1.
  apply eq1. apply eq0.
Qed.


Theorem silly2a : ∀ (n m  : nat), (n, n) = (m, m) →
                                  (∀ (q r : nat), (q, q) = (r, r) → [q] = [r]) →
                                  [n] = [m].
Proof.
  intros n m eqPair eqList.
  apply eqList. apply eqPair.
Qed.
(* apply is like a rewrite from the right hand side of the implies to the left *)
Theorem silly_ex : ∀ (p : nat),
    (∀ (n : nat), even n = true → even (S n) = false) →
    (∀ (n : nat), even n = false → odd n = true) →
    even p = true → odd (S p) = true.
Proof.
  intros p ev od evIod.
  apply od.
  apply ev.
  apply evIod.
Qed.

Theorem silly3 : ∀ (n m : nat),
    n = m →
    m = n.
Proof.
  intros n m eq.
  (* symmetry to switch left and right of equal sign *)
  symmetry.
  apply eq.
Qed.

Theorem rev_exercise1 : ∀ (l l' : list nat),
    l = rev l' →
    l' = rev l.

Proof.
  intros l l' leqrev.
  Search rev.
  rewrite -> leqrev.
  symmetry.
  apply rev_involutive.
Qed.

(* Proof. *)
(*   intros l l' leqrev. *)
(*   symmetry. *)
(*   rewrite <- rev_involutive. *)
(*   symmetry. *)
(*   rewrite leqrev. *)
(*   reflexivity. *)
(* Qed. *)


Theorem trans_eq : ∀ (X : Type) (n m o : X),
    n = m →
    m = o →
    n = o.
Proof.
  intros X n m o eq0 eq1.
  rewrite <- eq1.
  rewrite <- eq0.
  reflexivity.
Qed.


Example trans_eq_example : ∀ (a b c d e f : nat),
    [a;b] = [c; d] →
    [c;d] = [e;f] →
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq0 eq1.
  apply trans_eq with (m:=[c;d]).
  apply eq0.
  apply eq1.
Qed.

Example trans_eq_example' : ∀ (a b c d e f : nat),
    [a;b] = [c; d] →
    [c;d] = [e;f] →
    [a;b] = [e;f].
Proof.
  intros a b c d e f eq0 eq1.
  transitivity [c;d].
  apply eq0.
  apply eq1.
Qed.
Definition minustwo (a : nat) :=
  match a with
  | S (S a') => a'
  | _ => O
  end.

Example trans_eq_exercise : ∀ (a b c d : nat),
    (a + b) = c →
     c = (minustwo d) →
    (a + b) = (minustwo d).
Proof.
  intros a b c d.
  intros h i.
  transitivity c.
  apply h.
  apply i. (* exact i. *)
Qed.

Theorem S_injective : ∀ (n m : nat),
    S n = S m →
    n = m.
Proof.
  intros n m.
  intros eq0.
  assert (H: n = pred (S n)). { reflexivity. }
  rewrite -> H.
  rewrite -> eq0.
  simpl.
  reflexivity.
Qed.

Theorem S_injective' : ∀ (n m : nat),
    S n = S m →
    n = m.
Proof.
  intros n m H.
  injection H as H'.
  apply H'.
Qed.

Theorem injection_ex : ∀ (n m o : nat),
    [n;m] = [o;o] →
    n = m.
Proof.
  intros n m o.
  intros H.
  injection H as H'.
  rewrite H'.
  rewrite H.
  reflexivity.
Qed.

Example injection_ex3 : ∀ {X : Type} (x y z : X) (l j : list X),
    x :: y :: l = z :: j →
    j = z :: l →
    x = y.
Proof.
  intros X x y z l j.
  intros H I.
  injection H as H'.
  (* rewrite I in H. *)
  assert (J : y :: l = z :: l). { rewrite -> H. rewrite <- I. reflexivity. }
  injection J as H''.
  rewrite H'. rewrite H''.
  reflexivity.
Qed.
  
Theorem discriminate_ex1 : ∀ (n m : nat),
    false = true →
    n = m.
Proof.
  intros n m contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 : ∀ (n : nat),
    S n = O →
    2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

Example discriminate_ex3 : ∀ {X : Type} (x y z : X) (l j : list X),
    x :: y :: l = [] →
    x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
Qed.

Theorem eqb_0_l : ∀ n,
    0 =? n = true →
    n = 0.
Proof.
  intros n eq.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - discriminate eq.
Qed.
Theorem f_equal : ∀ {A B : Type} (f : A → B) (x y : A),
    x = y →
    f x = f y.
Proof.
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal : ∀ (n m : nat),
    n = m →
    S n = S m.
Proof.
  intros n m eq.
  apply f_equal.
  apply eq.
Qed.

(* simpl in *)
Theorem S_inj : ∀ (n m : nat) (b : bool),
    ((S n) =? (S m)) = b →
    (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

(* apply in, foward proof *)
Theorem silly4 : ∀ (n m p q : nat),
    (n = m → p = q) →
    m = n →
    q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H.
  apply EQ in H.
  symmetry in H.
  apply H.
Qed.

Theorem specialize_example : ∀ n,
    (∀ m, m * n = 0) →
    n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite Nat.add_comm in H.
  simpl in H.
  apply H.
Qed.


Theorem trans_eq_example''' : ∀ ( a b c d e f : nat),
    [a;b] = [c;d] →
    [c;d] = [e;f] →
    [a;b] = [e;f].
Proof.
  intros a b c d e f.
  intros eq0 eq1.
  specialize trans_eq with (m := [c;d]) as H.
  apply H.
  apply eq0.
  apply eq1.
Qed.

Theorem double_injective_failed : ∀ (n m : nat),
    double n = double m →
    n = m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. intros eq. destruct m as [|m' ] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct m as [|m' ] eqn:E.
    + discriminate eq.
    + f_equal.
Abort.


(* Theorem double_injective : ∀ (n m : nat), *)
(*     double n = double m → *)
(*     n = m. *)
(* Proof. *)
(*   intros n. *)
(*   induction n as [|n' IHn']. *)
(*   - simpl. intros m eq. destruct m as [|m' ] eqn:E. *)
(*     + reflexivity. *)
(*     + discriminate eq. *)
(*   - intros m eq. destruct m as [|m'] eqn:E. *)
(*      + discriminate eq. *)
(*     + f_equal. apply IHn'. simpl in eq. injection eq as goal. apply goal. *)

