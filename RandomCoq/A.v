(* very important *)
From Coq Require Import Unicode.Utf8.

Goal ∀ X Y : Prop, X → Y → X.

Proof.
  intros X Y. exact (fun A : X => fun B : Y => A).
  (* intros X Y A B. *)
  (* exact A. *)
Qed.

Goal ∀ X Y Z : Prop, (X → Y) → (Y → Z) → (X → Z).
Proof.
  intros X Y Z A B C.
  (* exact (B (A C)). *)

  (* apply B. *)
  (* apply A. *)
  apply B, A, C.
  Show Proof.
  (* exact C. *)
Qed.


Goal ∀ X Y Z : Prop, (X → Y → Z) → (X → Y) → (X → Z).

Proof.
  intros X Y Z A B C.
  (* exact (A C (B C)). *)
  apply A.
  - exact C.
  - apply B, C.
Qed.


(* ~ P ≅ P -> False *)
Goal ∀ X Y : Prop, (X → Y) → ¬ Y -> ¬ X.

Proof.
  intros X Y A B C.
  apply B, A, C.
Qed.
