From Coq Require Import Unicode.Utf8.
From Coq Require Import List.

Theorem listx0 : ∀ { X : Type} (l0 l1 : list X),
    rev (l0 ++ l1) = rev l1 ++ rev l0.
Proof.
  intros X l0.
  induction l0.
  - intros. simpl. Search "++". rewrite -> app_nil_r. reflexivity.
  - intros. simpl. rewrite -> IHl0. Search "++". rewrite app_assoc. reflexivity.
Qed.

  
Theorem rev_rev_n_eq_n : ∀ {X : Type} (l : list X),
    rev (rev l) = l.
Proof.
  intros X l.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite listx0. rewrite -> IHl. simpl. reflexivity.
Qed.

Theorem nat0 : ∀ x y : nat,
    S (S x + y) = S (S (x + y)).
Proof.
  intros.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite <- IHx. reflexivity.
Qed.

Theorem nat1 : ∀ x y : nat,
    S (x + y) = S x + y.
Proof.
  intros.
  induction x.
  - simpl. reflexivity.
  - rewrite <- IHx. simpl. reflexivity.
Qed.

Theorem nat2 : ∀ x y : nat,
    x + S y = S (x + y).
Proof.
  intros x y.
  induction x.
  - simpl. reflexivity.
  - rewrite -> nat0. rewrite <- IHx. rewrite -> nat1. reflexivity.
Qed.

Theorem nat3 : ∀ x y : nat,
    S x * y = x * y + y.
Proof.
  intros.
  induction x.
  - simpl.  Search "+". rewrite PeanoNat.Nat.add_0_r. reflexivity.
  - simpl.  rewrite -> PeanoNat.Nat.add_comm. reflexivity.
Qed.


Theorem nat4 : ∀ x y : nat,
    x * S y = x * y + x.
Proof.
  intros.
  induction x.
  - simpl.  reflexivity.
  - simpl. rewrite IHx. rewrite -> nat2.  rewrite -> PeanoNat.Nat.add_assoc. reflexivity.
  (* - rewrite nat3. rewrite nat3. rewrite IHx. rewrite -> nat2.  rewrite -> nat2. rewrite PeanoNat.Nat.add_comm. . reflexivity. *)

    
Qed. 

Theorem nat5 : ∀ x y : nat,
    x * y = y * x.
Proof.
  intros.
  induction x.
  - simpl. Search "*". rewrite -> PeanoNat.Nat.mul_0_r. reflexivity.
  - rewrite nat3. rewrite nat4. rewrite IHx. reflexivity.
