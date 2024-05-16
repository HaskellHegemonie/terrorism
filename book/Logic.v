From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.
From Coq Require Import Bool.
(* Fixpoint eqb (n m : nat) : bool := *)
(*   match n, m with *)
(*   | O, O => true *)
(*   | S n', S m' => eqb n' m' *)
(*   | _, _ => false *)
(*   end. *)

Axiom functional_extensionality : ∀ {X Y : Type}
                                    {f g : X → Y},
    (∀ (x : X), f x = g x) → f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros.
  induction x. reflexivity. simpl. rewrite IHx. reflexivity.
Qed.
Print Assumptions functional_extensionality.

Theorem restricted_excluded_middle : ∀ P b,
    (P ↔ b = true) → P ∨ ¬ P.
Proof.
  intros P b [A B].
  destruct b.
  - left. apply B. reflexivity.
  - right. unfold not. intros. discriminate A. apply H.
Qed.

Theorem restricted_excluded_middle_eq : ∀ (n m : nat),
    n = m ∨ n ≠ m.
Proof.
  intros.
  apply (restricted_excluded_middle (n = m) (n =? m)).
Admitted.


  
Theorem excluded_middle_irrefutable: ∀ (P : Prop),
    ¬ ¬ (P ∨ ¬ P).
Proof.
  intros.
  unfold not.
  intros.
  apply H.
  (* apply restricted_excluded_middle. *)
Admitted.


Record a := {b : nat }.

Definition s := a { b = 2 }.

