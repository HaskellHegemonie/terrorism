From Coq Require Export Unicode.Utf8.
Inductive natprod : Type :=
| pair (n1 n2 : nat).

Check (pair 3 5).

Definition fst (np : natprod) : nat :=
  match np with
  | pair x _ => x
  end.

Definition snd (np : natprod) : nat :=
  match np with
  | pair _ y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (np : natprod) : nat :=
  match np with
  | (x,_) => x
  end.

Definition snd' (np : natprod) : nat :=
  match np with
  | (_, y) => y
  end.

Definition swap_pair (np : natprod) : natprod :=
  match np with
  | (x, y) => (y, x)
  end.

Theorem surjective_pairing' : ∀ (n m : nat), (n, m) = (fst (n, m), snd (n, m)).
Proof.
  intros n m.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : ∀ (p : natprod), p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [x y].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : ∀ (p : natprod), (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [x y].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : ∀ (p : natprod), fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [x y].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
| nil
| cons (n : nat) (ns : natlist).

Definition myList := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: y" := (cons x y).
Notation "[ ]" := (nil).
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition myList1 := 1 :: 2 :: 3 :: nil.
Definition myList2 := [1, 2, 3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S c' =>  n :: repeat n c'
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
  | [] => 0
  | _ :: l' => S (length l')
  end.

Compute length myList2.


Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | a :: l => a :: append l l2
  end.


Definition head (default : nat) (np : natlist) : nat :=
  match np with
  | nil => default
  | a :: _ => a
  end.

Definition tail (l : natlist) : natlist :=
  match l with
  | nil => nil
  | _ :: l' => l'
  end.

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | nil => nil
  | a :: l' => match a with
               | O => nonzeros l'
               | S _ => a :: nonzeros l'
               end
  end.

Compute nonzeros [0,1,0,2,3,0,0].

Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Fixpoint is_even (n : nat) : bool :=
  match n with
  | O => true
  | S n => notb (is_even n)
  end.

Fixpoint oddmembers (np : natlist) : natlist :=
  match np with
  | nil => nil
  | a :: l' => match (is_even a) with
               | true => oddmembers l'
               | false => a :: oddmembers l'
               end
end.

Compute oddmembers [0,1,0,2,3,0,0].

(* Notation "x $ y" := (x y) (at level 50, left associativity). *)
Definition countoddmembers (np : natlist) : nat := length (oddmembers np).

Notation "x ++ y" := (append x y) (right associativity, at level 60).
Theorem app_assoc : ∀ l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [|hed tayl IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.
