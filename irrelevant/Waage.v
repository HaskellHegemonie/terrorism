From Coq Require Import Unicode.Utf8.
From Coq Require Import Nat.


Theorem plus_inj : ∀ x y z : nat,
    x + z = y + z → x = y.
Proof.
  intros.
  induction x.
  - simpl in H. induction z. rewrite -> H. simpl. symmetry. apply plus_n_O.
    rewrite IHz. reflexivity. Search "+". rewrite <- plus_n_Sm in H. injection H.
    intros. apply H0.
  - simpl in H. induction z. rewrite <- plus_n_O in H. rewrite <- plus_n_O in H. apply H.
    apply IHz.
    rewrite <- plus_n_Sm in H.
    rewrite <- plus_n_Sm in H.
    injection H.
    intros. apply H0.
    intros.
    apply IHx.
    rewrite <- plus_n_Sm.
    rewrite <- plus_n_Sm.
    rewrite H0. reflexivity.
Qed.

Theorem five_eq : 5 = 5. Proof. reflexivity. Qed.
Theorem easy_inj : 0 = 0.
Proof.
  apply (plus_inj _ _ 5).
  simpl. apply five_eq.
Qed.
