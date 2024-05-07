From Coq Require Import Unicode.Utf8.

(* Inductive nat := *)
(* | O *)
(* | S (n : nat). *)

(* Fixpoint add (n m : nat) : nat := *)
(*   match n with *)
(*   | O => m *)
(*   | S n' => S (add n' m) *)
(*   end. *)

Theorem plus_n_O : ∀ n : nat, plus n O = n.
Proof.
  intros n.
  induction n.
  (* 0 + x = x *)
  - unfold plus. reflexivity.
  (* S x + y = S (x + y) *)
  - unfold plus. fold plus. rewrite IHn. reflexivity.
Qed.
  

Theorem plus_0_n : ∀ n : nat, plus 0  n = n.
Proof.
  intros n.
  unfold plus.
  reflexivity.
Qed.

Theorem plus_n_0 : ∀ n : nat, plus n 0 = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem res0: ∀ n m : nat, n + S m = S (n + m).
Proof.
  intros n m.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

  

Theorem plus_comm: ∀ n m : nat, plus n m = plus m n.
Proof.
  intros n m.
  induction n.
  - rewrite plus_0_n. rewrite plus_n_0. reflexivity.
  - simpl. rewrite res0. rewrite IHn. reflexivity.
Qed.




Theorem mult_n_0 : ∀ n : nat, mult n 0 = 0.
Proof.
  intros n.
  induction n.
  - reflexivity.
    (* - unfold mult. 0 + mul n' m = 0 *)
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mult0 : ∀ n m : nat, mult n (S m) = n + mult n m.
Proof.
  intros n m.
  induction n.
  - simpl. reflexivity.
  - simpl.
Admitted.

  
Check mult.
Theorem mult_comm : ∀ n m : nat, mult n m = mult m n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite mult_n_0. reflexivity.
  - simpl. rewrite mult0. rewrite IHn. reflexivity.
Qed.

(* TODO: manually unfold *)
