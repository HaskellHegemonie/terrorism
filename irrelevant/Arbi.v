From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.
From Coq Require Import List.
Theorem app_nil_nothing : ∀ (X : Type) (l0 : list X),
    l0 ++ nil = l0.
Proof.
  intros X l0.
  induction l0.
  - reflexivity.
  - simpl. rewrite IHl0. reflexivity.
Qed.

Theorem app_assoc : ∀ (X : Type) (l0 l1 l2 : list X),
    (l0 ++ l1) ++ l2 = l0 ++ (l1 ++ l2).
Proof.
  intros X l0 l1 l2.
  induction l0.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl0. reflexivity.
Qed.

Theorem rev_reduce : ∀ (X : Type) (l0 l1 : list X),
    rev (l0 ++ l1) = rev l1 ++ rev l0.
Proof.
  intros X l0 l1.
  induction l0.
  - simpl. rewrite -> app_nil_nothing. reflexivity.
  - simpl. rewrite -> IHl0.  rewrite app_assoc. reflexivity.
Qed.

  
Theorem rev_rev_is_same : ∀ (X : Type) (l0 : list X),
    rev (rev l0) = l0.
Proof.
  intros X l0.
  induction l0.
  - reflexivity.
  - simpl. rewrite rev_reduce. simpl. rewrite IHl0. reflexivity.
Qed.
