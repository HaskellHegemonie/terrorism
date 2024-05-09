From Coq Require Import Unicode.Utf8.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : ∀ m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.



Fixpoint id_nat (n : nat) :=
  match n with
  | O => 0
  | S n => S (id_nat n)
  end.

Theorem x_id_nat_x : ∀ n : nat,
    n = id_nat n.
Proof.
  intros n.
  induction n.
  - unfold id_nat. reflexivity.
  (* https://coq.inria.fr/doc/v8.13/refman/proofs/writing-proofs/rewriting.html#grammar-token-reference_occs *)
  (* why does this work? *)
  (* - cbn. *)
  (* - pattern id_nat. *)
  - unfold id_nat. fold id_nat. rewrite <- IHn. reflexivity.
Qed.
