From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.

CoInductive stream { A : Type } : Type :=
| Cons : A → stream → stream.


CoFixpoint zeroes : stream := Cons 0 zeroes.

CoFixpoint true_falses : @stream bool := Cons true false_trues
with
false_trues := Cons false true_falses.


CoFixpoint map { A B : Type } (f : A → B) (s : @stream A) : @stream B :=
  match s with
  | Cons x xs => Cons (f x) (map f xs)
  end.


CoFixpoint interleave { A : Type } (s0 s1 : @stream A) : @stream A :=
  match s0, s1 with
  | Cons x xs, Cons y ys => Cons x (Cons y (interleave xs ys))
  end.


Definition var := nat.
Check var.
Compute var.
  
