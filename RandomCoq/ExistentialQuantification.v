From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.
Inductive ex (X : Type) (P : X -> Prop) : Prop :=
  ex_intro : forall witness:X, P witness -> ex X P.

Check ex_intro.

Check ex_intro nat (fun x => x = 2) 2.
