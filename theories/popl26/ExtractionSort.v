From Corelib Require Import LargeElim.

Sort Info Erase.

(* Constraints on Type are added for large elimination *)
Constraint Info ~> Erase, Info ~> Type, Erase ~> Type.

Set Universe Polymorphism.

Lemma nat_discr_info (n : nat@{Info;}): O = S n -> False.
Proof.
  apply (nat_discr n).
Qed.

Lemma nat_discr_erase (n : nat@{Erase;}): O = S n -> False.
Proof.
  apply (nat_discr n).
Qed.

Inductive Vect (A : 𝒰@{Info;_}) : nat@{Erase;} -> 𝒰@{Info;_} :=
| vnil : Vect A O
| vcons : forall (a:A) n, Vect A n -> Vect A (S n).

Fail Definition length_cheat A n : Vect A n -> nat@{Info;} := fun _ => n.

Definition length' A n : Vect A n -> nat := fun _ => n.

Fixpoint length A n : Vect A n -> nat@{Info;} :=
  fun v => match v with
    | vnil _ => O
    | vcons _  a n v => S (length A n v)
    end.

Fail Definition vector_from_info_nat A (n:nat@{Info;}) : Vect A n.

Fixpoint info_to_erase (n : nat@{Info;}) : nat@{Erase;} :=
    match n with O => O | S n => S (info_to_erase n) end.

Fail Fixpoint erase_to_info (n : nat@{Erase;}) : nat@{Info;} :=
    match n with O => O | S n => S (erase_to_info n) end.
