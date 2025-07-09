Require Import Notations.
Require Import Ltac.
Require Import Logic.

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

(* Example of Large Elimination on natural numbers *)

Inductive nat : 𝒰 :=
  | O : nat
  | S : nat -> nat.

Inductive unit : 𝒰 := tt.
Inductive empty : 𝒰 := .

Definition nat_rect@{i} := nat_poly@{Type Type; i}.
Definition nat_rec@{} := nat_poly@{Type Type; 0}.
Definition nat_ind@{} := nat_poly@{Type Prop; 0}.
Definition nat_sind@{} := nat_poly@{Type SProp; 0}.


Definition P@{s;l |Type~>s} {H:LargeElimSort@{s;l}} (n : nat@{s;}) :=
  match n return H.(Univ) with
    O => code unit
  | _ => code empty
  end.

Lemma eq_true@{s;l |Type~>s} {H:LargeElimSort@{s;l}} : forall (n:nat), O = n -> H.(El) (P n).
Proof.
  intros b e. destruct e. exact (lift_El _ tt).
Qed.

Lemma nat_discr_gen@{s;l |Type~>s} {H:LargeElimSort@{s;l}} (n : nat@{s;}) : O = S n -> empty@{s;0_}.
Proof.
  intro e. exact (unlift_El _ (eq_true _ e)).
Qed.

(* Direct Large Elimination *)

Definition Pred_nat@{s ; | s ~> Type} (n : nat@{s;}) :=
  match n return Type with | O => unit | _ => empty end.

Lemma eq_true'@{s ; | s ~> Type} : forall (n:nat), O = n -> Pred_nat@{s ; } n.
Proof.
  intros b e. destruct e. exact tt.
Qed.

Lemma nat_discr@{s ; | s ~> Type} (n : nat@{s;}) : O = S n -> False.
Proof.
  intro e. destruct (eq_true' _ e).
Qed.
