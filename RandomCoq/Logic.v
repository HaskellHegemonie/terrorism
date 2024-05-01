From Coq Require Import Unicode.Utf8.
Example and_exercise :
  ∀ n m : nat, n + m = 0 → n = 0 ∧ m = 0.
Proof.
  intros n m H.
  (* maybe something with ~spcialize~? *)
  assert (I : n = 0). { destruct n. reflexivity. discriminate H. }
  split.
  - apply I.
  - destruct m. reflexivity. rewrite <- H. rewrite -> I. reflexivity.
Qed.

Lemma proj2 : ∀ P Q : Prop,
    P ∧ Q → Q.
Proof.
  intros p q [ _ Q ].
  apply Q.
Qed.

Theorem and_assoc : ∀ P Q R : Prop,
    P ∧ (Q ∧ R) → (P ∧ Q) ∧ R.
Proof.
  intros p q r [P [Q R]].
  split.
  - split. apply P. apply Q.
  - apply R.
Qed.
       
Lemma factor_is_O:
  ∀ n m : nat, n = 0 ∨ m = 0 → n * m = 0.
Proof.
  assert (H: ∀ x : nat, x * 0 = 0). { induction x. reflexivity. simpl. rewrite -> IHx. reflexivity. }
  intros n m [nO | mO ].
  - rewrite -> nO. reflexivity.
  - rewrite -> mO. Search "*". apply H.
Qed.


Lemma or_intro_l : ∀ A B : Prop, A → A ∨ B.
Proof.
  intros A B A'.
  left. apply A'.
Qed.


Lemma zero_or_succ :
  ∀ n : nat, n = 0 ∨ n = S (pred n).
Proof.
  intros n.
  destruct n.
  - left. reflexivity.
  - right. reflexivity.
  
Qed.

Lemma mult_is_O :
  ∀ n m, n * m = 0 → n = 0 ∨ m = 0.
Proof.
  intros n m.
  destruct n.
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + discriminate H.
Qed.

                                    
Theorem or_commut : ∀ P Q : Prop,
    P ∨ Q → Q ∨ P.
Proof.
  intros p q [ P | Q ].
  - right. apply P.
  - left. apply Q.
Qed.

(* ¬ P ≅ ∀ Q, P → Q. *)
(* but in Coq: ¬ P ≅ P → False *)

Theorem ex_falso_quodlibet : ∀ (P:Prop),
    False → P.
Proof.
  intros p fals.
  destruct fals.
Qed.

Theorem not_implies_our_not : ∀ (P:Prop),
    ¬ P → (∀ (Q:Prop), P → Q).
Proof.
  intros P nP Q H.
  (* unfold not. *)
  destruct nP.
  apply H.
Qed.

