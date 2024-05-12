From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.
From Coq Require Import List.
From Coq Require Import Bool.

Theorem function_equality_x1 :
  (fun x => 3 + x) = (fun x => pred 4 + x).
Proof.
  reflexivity.
Qed.

Axiom functional_extensionality : ∀ {X Y: Type}
                                    {f g : X → Y},
    (∀ (x:X), f x = g x) → f = g.


Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros.
  Search "+".
  rewrite  (PeanoNat.Nat.add_comm 1 x).
  reflexivity.
Qed.

Fixpoint rev_append {X : Type} (l0 l1 : list X) : list X :=
  match l0 with
  | nil => l1
  | x :: l' => rev_append l' (x :: l1)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l nil.

Theorem ex1 : ∀ X (l0 l1 : list X),
    rev_append l0 l1 = rev l0 ++ l1.
Proof.
  induction l0.
  - reflexivity.
  - intros. simpl. rewrite IHl0. Search "++". rewrite <- app_assoc. rewrite <- app_comm_cons. reflexivity.
   (* app_comm_cons: ∀ (A : Type) (x y : list A) (a : A), a :: x ++ y = (a :: x) ++ y *)
Qed.

Theorem tr_rev_correct : ∀ X, @tr_rev X = @rev X.
Proof.
  intros.
  apply functional_extensionality.
  intros. induction x.
  - reflexivity.
  - unfold tr_rev. simpl. rewrite ex1. reflexivity.
Qed.

Theorem restricted_excluded_middle : ∀ P b,
    (P ↔ b = true) → P ∨ ¬ P.
Proof.
  intros P [] [p b].
  - left. apply b. reflexivity.
  - right. unfold not. intros. apply p in b. discriminate. apply p, H.
Qed.

