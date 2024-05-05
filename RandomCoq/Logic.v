From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.
From Coq Require Import List.
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

Notation "x <> y" := (¬ (x = y)). 
(* ugly *)

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros contra.
  discriminate contra.
Qed.

Theorem not_False : ¬ False.
Proof.
  unfold not.
  intros n.
  apply n.
Qed.

Theorem contradiction_implies_anything : ∀ P Q : Prop,
    (P ∧ ¬ P) → Q.
Proof.
  intros p q [P NP].
  unfold not in NP.
  apply NP in P.
  destruct P.
Qed.

Theorem double_neg : ∀ P : Prop,
    P → ¬ ¬ P.
Proof.
  intros p P.
  unfold not.
  intros NP.
  (* apply with contradiction_implies_anything? *)
  apply NP, P.
Qed.

Theorem contrapositive : ∀ (P Q : Prop),
    (P → Q) → (¬ Q → ¬ P).
Proof.
  intros p q PQ.
  unfold not.
  intros NQ P.
  apply NQ.
  apply PQ.
  apply P.
Qed.

Theorem not_both_true_and_false : ∀ P : Prop,
    ¬ (P ∧ ¬ P).
Proof.
  intros p.
  unfold not.
  intros [P NP].
  apply NP, P.
Qed.

Theorem de_morgan_not_or : ∀ (P Q : Prop),
    ¬ (P ∨ Q) → ¬ P ∧ ¬ Q.
Proof.
  intros p q.
  unfold not.
  intros H.
  split.
  - intros P.  apply H. left. apply P.
  - intros Q. apply H. right. apply Q.
Qed.

Theorem not_true_is_false : ∀ b : bool,
    b ≠ true → b = false.
Proof.
  intros b H.
  destruct b.
  + unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  + reflexivity.
Qed.

Theorem not_true_is_false': ∀ b : bool,
    b ≠ true → b = false.
Proof.
  intros b H.
  destruct b.
  + unfold not in H.
    exfalso.
    apply H. reflexivity.
  + reflexivity.
Qed.

Lemma Truth_is_true : True.
Proof.
  apply I.
Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : ∀ n,
    ¬ (O = S n).
Proof.
  intros n.
  unfold not.
  intros H.
  assert (I : disc_fn O). { unfold disc_fn. apply I. }
  rewrite H in I.
  unfold disc_fn in I.
  apply I.
Qed.

(* Definition iff (P Q : Prop) := (P → Q) ∧ (Q → P). *)
(* Notation "P <-> Q" := (iff P Q) *)
(*                       (at level 95, no associativity) *)
(*                       : type_scope. *)

Theorem iff_sym : ∀ P Q : Prop,
    (P ↔ Q) → (Q ↔ P).
Proof.
  intros p q.
  intros [PQ QP].
  unfold iff.
  split.
  - intros Q. apply QP, Q.
  -  intros P. apply PQ, P.
Qed.



Theorem not_true_iff_false: ∀ b : bool,
    b ≠ true ↔ b = false.
Proof.
  intros b.
  unfold iff.
  split.
  + apply not_true_is_false.
  + unfold not. intros NB BT.
    rewrite NB in BT.
    (* discriminate is used when the hypothesis is wrong. Like in this case false = true*)
    discriminate BT.
Qed.
Lemma apply_iff_example1:
  ∀ P Q R : Prop, (P ↔ Q) → (Q → R) → (P → R).
Proof.
  intros p q r.
  intros pFq qr P.
  apply qr, pFq, P.
Qed.

Lemma apply_iff_example2:
  ∀ P Q R : Prop, (P ↔ Q) → (P → R) → (Q → R).
Proof.
  intros p q r.
  intros pq pr Q.
  apply pr, pq, Q.
Qed.

Theorem or_distributes_over_and : ∀ P Q R : Prop,
    P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R).
Proof.
  intros p q r.
  unfold iff.
  split.
  + intros [ P | [Q R]].
  - split. left. apply P. left. apply P.
  - split. right. apply Q. right. apply R.
    +  intros [[P | Q] [P' | R]].
  - left. apply P.
  - left. apply P.
  - left. apply P'.
  - right. split. apply Q. apply R.
Qed.
(* https://www.youtube.com/watch?v=HvOCttTKZwk *)
(* your mama's a setoid *)

Definition Even (n : nat) := ∃ x : nat, n = double x.
Theorem four_is_Even : Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : ∀ n,
  (∃ m, n = 4 + m) →
  (∃ o, n = 2 + o).
Proof.
  intros n [m H].
  exists (2 + m).
  apply H.
Qed.

Theorem dist_not_exists : ∀ (X:Type) (P : X → Prop),
    (∀ x, P x) → ¬ (∃ x, ¬ P x).
  intros x p H.
  unfold not.
  intros [x0 I].
  apply I, H.
Qed.

Theorem dist_exists_or : ∀ (X:Type) (P Q : X → Prop),
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x).
Proof.
  intros x p q.
  split.
  - intros [x0 [H | H] ].
    + left.  exists x0. apply H.
    + right. exists x0. apply H.
  - intros [[x0 H] | [x0 H]].
    + exists x0. left. apply H.
    + exists x0. right. apply H.
Qed.

(* Theorem leb_plus_exists : ∀ n m, n <=? m = true → ∃ x, m = n+x. *)
(* Proof. *)
(*   intros n m H. *)
(*   destruct H as [|Hle]. *)
(*   - exists m. reflexivity. *)
(*   - intros.  *)

Theorem assoc_plus_minus : ∀ n m u : nat,
    (* u <=? m = true → *) n + (m - u) = n + m - u.
Proof.
  intros.
  induction n.
  simpl. reflexivity.
  simpl. rewrite IHn.
  destruct u.
  - Search "-". rewrite PeanoNat.Nat.sub_0_r. reflexivity.
  - Search "-".
Admitted.

Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n + x.
Proof.
  intros n m H.
  exists (m - n).
  induction n.
  - simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
  - simpl. Search "-". rewrite assoc_plus_minus. 
Admitted.  

Fixpoint In { X : Type } (x : X) (l : list X) : Prop :=
  match l with
  | nil => False
  | y :: ys => x = y ∨ In x ys
  end.
  
Theorem plus_exists_leb : ∀ n m, (∃ x, m = n+x) → n <=? m = true.
Proof.
  intros n m [x H].
