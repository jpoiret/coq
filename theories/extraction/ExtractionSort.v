Sort Extr.

Constraint Extr ~> SProp.
Constraint Type ~> Extr.

Set Universe Polymorphism.
Set Sort Polymorphism.

Class LargeElimSort@{s t; l| t ~> Type} : 𝒰@{t;l+2} :=
{ Univ : 𝒰@{s;l+1} ;
  code : 𝒰@{s;l} -> Univ ;   
  El : Univ -> 𝒰@{s;l} ;
  El_code A : El (code A) = A :> 𝒰@{s;l} }.

Definition lift_El@{s;u} {H:LargeElimSort@{s Type;u}} (A:𝒰@{s;u}) : A -> H.(El) (H.(code) A) :=
  fun a => eq_poly _ (fun X => X) a _ (eq_sym (H.(El_code) A)).

Definition unlift_El@{s;u} {H:LargeElimSort@{s Type;u}} (A:𝒰@{s;u}) : H.(El) (H.(code) A) -> A :=
  fun a => eq_poly _ (fun X => X) a _ (H.(El_code) _).

Instance ExtrLargeElimSort@{l} : LargeElimSort@{Extr Type; l}.
Admitted. 

Inductive nat : 𝒰 :=
  | O : nat
  | S : nat -> nat.

Inductive unit : 𝒰 := tt.
Inductive empty : 𝒰 := .

Definition nat_rect@{i} := nat_poly@{Type Type; i}.
Definition nat_rec@{} := nat_poly@{Type Type; 0}.
Definition nat_ind@{} := nat_poly@{Type Prop; 0}.
Definition nat_sind@{} := nat_poly@{Type SProp; 0}.

Definition P@{s;u} {H:LargeElimSort@{s Type;u}} (n : nat@{s;}) :=
  match n return H.(Univ) with
    O => code unit@{s;u}
  | _ => code empty@{s;u}
  end.

Lemma eq_true@{s;u} {H:LargeElimSort@{s Type;u}} : forall (n:nat@{s;}), O = n -> H.(El) (P n).
Proof.
  intros b e. destruct e. exact (lift_El _ tt).
Qed.

Lemma nat_discr@{s;u} {H:LargeElimSort@{s Type;u}} (n : nat@{s;}): O = S n -> empty@{s;u}.
Proof.
  intro e. exact (unlift_El _ (eq_true _ e)).
Qed.

Lemma nat_discr_extr (n : nat@{Extr;}): O = S n -> False.
Proof.
  intro e. pose proof (nat_discr n e). destruct X.
Qed.  

Inductive Vect (A : Type) : nat@{Extr;} -> Type :=
| vnil : Vect A O
| vcons : forall (a:A) n, Vect A n -> Vect A (S n).

Fail Definition length A n : Vect A n -> nat@{Type;} := fun _ => n. 

Fixpoint length A n : Vect A n -> nat@{Type;} := 
  fun v => match v with 
    | vnil _ => O 
    | vcons _  a n v => S (length A n v)
    end.
