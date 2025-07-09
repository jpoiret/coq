Sort Info Erase.

Constraint Info ~> Erase, Info ~> Type, Erase ~> Type.

Set Universe Polymorphism.

Class LargeElimSort@{s;l|Type~>s} : Type@{l+2} :=
{ Univ : 𝒰@{s;l+1} ;
  code : 𝒰@{s;l} -> Univ ;   
  El : Univ -> 𝒰@{s;l} ;
  El_code A : El (code A) = A :> 𝒰@{s;l} }.

Instance TypeLargeElimSort@{l} : LargeElimSort@{Type;l} := {
    Univ := Type@{l} ; code := fun A => A ; El := fun A => A ; El_code := fun A => eq_refl}.

Definition lift_El@{s;l |Type~>s} {H:LargeElimSort@{s;l}} (A:𝒰@{s;l}) : A -> H.(El) (H.(code) A) :=
  fun a => eq_poly _ (fun X => X) a _ (eq_sym (H.(El_code) A)).

Definition unlift_El@{s;l |Type~>s} {H:LargeElimSort@{s;l}} (A:𝒰@{s;l}) : H.(El) (H.(code) A) -> A :=
  fun a => eq_poly _ (fun X => X) a _ (H.(El_code) _).


Inductive nat : 𝒰 :=
  | O : nat
  | S : nat -> nat.

Inductive unit : 𝒰 := tt.
Inductive empty : 𝒰 := .

Definition nat_rect@{i} := nat_poly@{Type Type; i}.
Definition nat_rec@{} := nat_poly@{Type Type; 0}.
Definition nat_ind@{} := nat_poly@{Type Prop; 0}.
Definition nat_sind@{} := nat_poly@{Type SProp; 0}.

(*
Definition P {H:LargeElimSort} (n : nat) :=
  match n return H.(Univ) with
    O => code unit
  | _ => code empty
  end.

Lemma eq_true {H:LargeElimSort} : forall (n:nat), O = n -> H.(El) (P n).
Proof.
  intros b e. destruct e. exact (lift_El _ tt).
Qed.

Lemma nat_discr_gen {H:LargeElimSort} (n : nat): O = S n -> empty.
Proof.
  intro e. exact (unlift_El _ (eq_true _ e)).
Qed.


Lemma nat_discr (n : nat@{Info;}): O = S n -> False.
Proof.
  intro e. pose proof (nat_discr_gen n e). destruct X.
Qed.
*)

Inductive Vect (A : 𝒰@{Info;_}) : nat@{Erase;} -> 𝒰@{Info;_} :=
| vnil : Vect A O
| vcons : forall (a:A) n, Vect A n -> Vect A (S n).

Fail Definition length A n : Vect A n -> nat@{Info;} := fun _ => n.

Definition length' A n : Vect A n -> nat := fun _ => n.

Fixpoint length A n : Vect A n -> nat@{Info;} :=
  fun v => match v with 
    | vnil _ => O 
    | vcons _  a n v => S (length A n v)
    end.

Fail Definition vector_from_commut_nat A (n:nat@{Info;}) : Vect A n.

Fixpoint info_to_erase (n : nat@{Info;}) : nat@{Erase;} :=
    match n with O => O | S n => S (info_to_erase n) end.

Definition vector_from_commut_nat A (n:nat@{Info;}) : Vect A (info_to_erase n).
Abort.
