From Coq Require Import Unicode.Utf8.
(* Inductive list (X : Type) : Type := *)
(* | nil *)
(* | cons (x : X) (l : list X). *)


Check @nil nat : list nat.
Check list.

Check @cons nat 3 (@nil nat) : list nat.

Check @nil : ∀ X : Type, list X.

Check @cons : ∀ X : Type, X → list X → list X.

Fixpoint repeat (X : Type) (x : X) (n : nat) :=
  match n with
  | 0 => @nil X
  | S n' => @cons X x (repeat X x n')
  end.

Inductive mumble : Type :=
| a
| b (x : mumble) (y : nat)
| c.

Inductive grumble (X : Type) : Type :=
| d (m : mumble)
| e (x : X).

(* Check d (b a 5). *)
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
(* Check e bool (b c 0). *)
Check c.
  
Fixpoint repeat' X x n :=
  match n with
  | O => @nil X
  | S n' => @cons X x (repeat' X x n')
  end.

(* Type holes with "_" *)

Fixpoint repeat'' X x n : list X :=
  match n with
  | O => @nil _
  | S n' => @cons _ x (repeat'' X x n')
  end.


(* Arguments @nil {X}. *)
(* Arguments @cons {X}. *)
(* Arguments @repeat{X}. *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(* also works for function definition *)
Fixpoint repeat''' {X : Type} x n : list X :=
  match n with
  | O => nil
  | S n' => cons x (repeat''' x n')
  end.

                                             
Fixpoint append {X : Type} l0 l1 : list X :=
  match l0 with
  | nil => l1
  | cons x xs => cons x (append xs l1)
  end.

Fixpoint rev {X : Type} (l0 : list X) : list X :=
  match l0 with
  | nil => nil
  | cons x xs => append (rev xs) (cons x nil)
  end.

Fixpoint length { X : Type } (l : list X) :=
  match l with
  | nil => O
  | cons _ xs => S (length xs)
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.


(* prefix with "@" forces the use of explicit types *)
Definition mynil := @nil nat.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (append x y)
                     (at level 60, right associativity).
Definition list123''' := [1; 2; 3].

(* Theorem app_nil_r : ∀ (X : Type), ∀ l : list X, l ++ [] = l. *)
Theorem app_nil_r : ∀ (X:Type), ∀ l:list X,
    l ++ [] = l.

Proof.
  intros X l.
  induction l as [|y ys IHy' ].
  - reflexivity.
  - simpl. rewrite -> IHy'. reflexivity.
Qed.

(* Theorem app_assoc : ∀ X : Type, ∀ a b c : list X, (a ++ b) ++ c = a ++ (b ++ c). *)
(* Proof. *)
(*   intros X a b c. *)
(*   induction a as [|y ys IHy']. *)
(*   (* don't know why reflexivity doesn't work, shows a "%" symbol  *) *)
(*   - simpl. reflexivity. *)
(*   - simpl.  rewrite -> IHy'. reflexivity. *)
(* Qed. *)

(* Lemma app_length : ∀ X : Type, ∀ l0 l1 : list X, length (l0 ++ l1) = length l0 + length l1. *)
(* Proof. *)
(*   intros X l0 l1. *)
(*   induction l0 as [|y ys IHy']. *)
(*   - simpl. reflexivity. *)
(*   - simpl. rewrite -> IHy'.  reflexivity. *)
(* Qed. *)

(* Theorem rev_app_distr : ∀ X (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1. *)
(* Proof. *)
(*   intros X l1 l2. *)
(*   induction l1 as [| y ys IHy']. *)
(*   - simpl. rewrite -> app_nil_r. reflexivity. *)
(*   - simpl. rewrite -> IHy'. rewrite -> app_assoc. *)
    

