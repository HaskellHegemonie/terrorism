From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.
From Coq Require Import List.
Require Init.Datatypes.
Require Import PeanoNat Le Gt Minus Bool Lt.
Theorem dist_not_exists : ∀ (X:Type) (P : X → Prop),
    (∀ x, P x) → ¬ (∃ x, ¬ P x).

Proof.
  intros X P xp.
  unfold not.
  intros [x pxfalse].
  apply pxfalse, xp.
Qed.

  
Theorem dist_exists_or : ∀ (X:Type) (P Q : X → Prop),
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x).
Proof.
  intros X P Q.
  split.
  intros [x [Px | Qx]].
  - left. exists x. apply Px.
  - right. exists x. apply Qx.
  - intros [[x Px] | [x  Qx]].
    + exists x. left. apply Px.
    + exists x. right. apply Qx.
Qed.

Theorem leb_plus_exists : ∀ n m, n <=? m = true → ∃ x, m = n+x.
Proof.
  intros n.
  induction n.
  - simpl.  intros. exists m. reflexivity.
  - destruct m.
    + intros.  discriminate H.
    + simpl. intros.  apply IHn in H. destruct H. exists x. rewrite <- H. reflexivity.

Qed.

Fixpoint In {X : Type} (x : X) (l : list X) : Prop :=
  match l with
  | nil => False
  | x' :: l' => x = x' ∨ In x l'
  end.

                                                          
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Example In_example_2 : ∀ n, In n [2; 4] →
                            ∃ n', n = 2 * n'.
Proof.
  intros n [two | [four | [] ] ].
  - exists 1. simpl. apply two.
  - exists 2. simpl. apply four.
Qed.

Theorem In_map : ∀ (A B : Type) (f : A → B) (l : list A) (x : A) ,
    In x l →
    In (f x) (map f l).

Proof.
  intros.
  induction l.
  - simpl. simpl in H. apply H.
  - simpl in H. simpl.
    destruct H.
    + left. rewrite H. reflexivity.
    + apply IHl in H. right. apply H.
Qed.

Theorem In_map_iff :
  ∀ (A B : Type) (f : A → B) (l : list A) (y : B),
         In y (map f l) ↔
           ∃ x, f x = y ∧ In x l.
Proof.
  intros A B f l y.
  split.
  - induction l.
    + simpl. contradiction.
    + simpl. intros [yfa | inmap].
      * exists a. split. rewrite yfa. reflexivity. left. reflexivity.
      * apply IHl in inmap. destruct inmap as [x [O T]].
        exists x. split. apply O. right. apply T.
  - intros [x [O T]]. rewrite <- O. apply In_map, T.
Qed.

Theorem In_app_iff : ∀ A l l' (a:A),
    In a (l++l') ↔ In a l ∨ In a l'.
Proof.
  intros A l. induction l as [|a' l' IH].
  - split. right. apply H. intros [H | H]. contradiction H. simpl. apply H.
  - intros. split.
Abort.

Fixpoint All (X : Type) (P : X → Prop) (l : list X) : Prop :=
  match l with
  | nil => True
  | x' :: l' => P x' ∧ All X P l'
  end.


Theorem All_In : ∀ (T : Type) (P : T → Prop) (l : list T),
    (∀ x : T, In x l → P x) ↔
      All T P l.
Proof.
  intros T P l.
  split.
  - induction l.
    + intros. simpl. apply I.
    + intros. simpl in H. simpl. split.
      * apply H. left. reflexivity. 
      * apply IHl. intros. apply H. right. apply H0.
  - induction l.
    + simpl. intros. contradiction.
    + simpl. intros [H I] x [xea | inl].
      * rewrite xea. apply H.
      * apply IHl. apply I. apply inl.
Qed.

Definition combine_odd_even (Podd Peven : nat → Prop) : nat → Prop :=
  fun x : nat => if odd x then Podd x else Peven x.

Theorem combine_odd_even_intro :
  ∀ (Podd Peven : nat → Prop) (n : nat),
    (odd n = true → Podd n) →
    (odd n = false → Peven n) →
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n.
  intros.
  unfold combine_odd_even.
  induction n.
  - simpl. apply H0. simpl. reflexivity.
  - destruct (odd (S n)).
    + apply H. reflexivity.
    + apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  ∀ (Podd Peven : nat → Prop) (n : nat),
    combine_odd_even Podd Peven n →
    odd n = true → Podd n.
Proof.
  unfold combine_odd_even.
  intros Podd Peven n.
  induction n.
  - intros. unfold odd in H0. simpl in H0. discriminate H0.
  - intros. destruct (odd (S n)).
    + apply H.
    + discriminate H0.
Qed.

Theorem combine_odd_even_elim_even :
  ∀ (Podd Peven : nat → Prop) (n : nat),
    combine_odd_even Podd Peven n →
    odd n = false →
    Peven n.
Proof.
  intros Podd Peven n.
  induction n.
  - intros. unfold combine_odd_even in H. apply H.
  - intros. unfold combine_odd_even in H. unfold combine_odd_even in IHn. destruct (odd (S n )).
    + discriminate H0.
    + apply H.
Qed.

Check plus.
Check @rev.
Check Nat.add_comm.

Theorem add_assoc' : ∀ x y z : nat,
    x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite Nat.add_comm.
  rewrite (Nat.add_comm y z).
  reflexivity.
Qed.
Theorem in_not_nil :∀ (A : Type) (x : A) (l : list A),
  In x l → l ≠ [].
(* Proof. *)
(*   intros A x l H. *)
(*   unfold not. *)
(*   intros H0. *)
(*   destruct l. *)
(*   - simpl in H. apply H. *)
(*   - discriminate H0. *)
(* Qed. *)
Proof.
  intros A x l H.
  unfold not.
  intros Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 : ∀ l : list nat,
    In 42 l → l ≠ [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
  Restart.
  intros l H.
  apply in_not_nil in H.
  apply H.
  Restart.
  intros l H.
  apply (in_not_nil nat 42), H.
  Restart.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Fixpoint mydouble (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (mydouble n))
  end.

Lemma even_double : ∀ k, even (mydouble k) = true.
Proof.
  intros k.
  induction k.
  - reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

Theorem ex0 : ∀ n : nat,
    even n = true → even (S n) ≠ true.
Proof.
  unfold not.
  intros.
  induction n.
  - rewrite <- H in H0. simpl in H0. discriminate H0.
  - apply IHn. rewrite <- H0. simpl. reflexivity. rewrite H. reflexivity.
Qed.

Lemma even_double_conv : ∀ n, ∃ k,
    n = if even n then mydouble k else S (mydouble k).
Proof.
  intros n.
  induction n.
  - exists 0. reflexivity.
  - destruct (even (n)) eqn:E.
    + destruct IHn as [k H]. destruct (even (S n)) eqn:E'.
      * exists k. rewrite <- H. exfalso. apply ex0 in E'. simpl in E'. rewrite <- E in E'.
        unfold not in E'. apply E'. reflexivity.
      * exists k. rewrite <- H. reflexivity.
    + destruct IHn as [k H]. destruct (even (S n)) eqn:E'.
      * exists (S k). simpl. rewrite -> H. reflexivity.
        (* * rewrite <- E' in E. rewrite H in E. *)
      * rewrite -> H in E'. simpl in E'. rewrite -> even_double in E'. discriminate E'.
Qed.

Definition Even (n : nat) := ∃ x : nat, n = mydouble x.

Theorem even_bool_prop : ∀ n,
    even n = true ↔ Even n.
Proof.
  split.
  - intros. destruct (even_double_conv n) as [k Hk].
    rewrite Hk.
    rewrite -> H. unfold Even.
    exists k.
    reflexivity.
  - unfold Even. intros [x H]. rewrite -> H. apply even_double.
Qed.
Search "eqb_true".
Search "eqb_refl".
Search "eqb_eq".
Search "eqb_nat".
Check eqb.
