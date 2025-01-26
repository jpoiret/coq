From Corelib Require Import Types.
From Corelib Require Import Classes.

Section GroupoidOperations.
  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {_leibniz: Has_Leibniz@{sa se se|la le le} eq} {_refl: Has_refl@{sa se|la le} eq}
          {A : Type@{sa|la}}.

  #[warnings="-notation-overridden"]
  Local Notation "x = y" := (eq _ x y) : type_scope.
  #[warnings="-notation-overridden"]
  Local Notation "x <> y" := (~ (eq _ x y)) : type_scope.

  Definition eq_sym {x y : A} (e : x = y) : y = x :=
    leibniz _ _ _ (fun y => y = x) (refl _ _) _ e.

  Definition eq_trans {x y z : A} (e1 : x = y) : y = z -> x = z :=
    fun e2 => leibniz _ _ _ (fun z => x = z) e1 _ e2.

  Definition not_eq_sym {x y : A} : x <> y -> y <> x :=
    fun ne e => ne (eq_sym e).

End GroupoidOperations.


(** Leibniz equality. *)
Section Leibniz.

  Sort sa se.
  Universe la le.
  Context {eq : forall A : Type@{sa | la}, A -> A -> Type@{se|le}}
          {_leibniz: Has_Leibniz@{sa se se|la le le} eq} {_refl: Has_refl@{sa se|la le} eq}
          {A : Type@{sa|la}}.

  Global Instance eq_Reflexive : Reflexive (@eq A) := refl A.
  Global Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym _ _ _ A.
  Global Instance eq_Transitive : Transitive (@eq A) := @eq_trans _ _ A.

(*  Lemma proper_ap : Proper (Proper (eq A ++> flip arrow) P). *)

    (** Leibinz equality [eq] is an equivalence relation.
        The instance has low priority as it is always applicable
        if only the type is constrained. *)

  Global Program Instance eq_equivalence : Equivalence (eq A) | 10.
End Leibniz.

Tactic Notation "symmetry_eq" := symmetry; try typeclasses eauto.
Tactic Notation "transitivity_eq" := transitivity; try typeclasses eauto.
Tactic Notation "transitivity_eq" constr(t) := transitivity t; try typeclasses eauto.

(* Aliases *)

Definition _eq_sym@{s s'|u} {A:Type@{s|u}} {x y : A} (e : x = y :> A : Type@{s'|u})
  : y = x :> A : Type@{s'|u} := @eq_sym (@eq@{s s'|u}) eq_Has_Leibniz_elim@{s s'|u u} _  A x y e.

Register _eq_sym as core.eq.sym.

Definition ind_eq_trans@{l} := @eq_trans@{Type Prop|l 0} (@eq) _.
Register ind_eq_trans as core.eq.trans.

Notation sym_eq := _eq_sym (only parsing).
Notation trans_eq := eq_trans (only parsing).
Notation sym_not_eq := not_eq_sym (only parsing).

Notation refl_equal := eq_refl (only parsing).
Notation sym_equal := _eq_sym (only parsing).
Notation trans_equal := eq_trans (only parsing).
Notation sym_not_equal := not_eq_sym (only parsing).

#[export]
Hint Immediate _eq_sym not_eq_sym: core.

Definition eq_elim_r@{sa se sp|la le lp|} {eq} (A:Type@{sa|la})
  `{Has_Leibniz@{sa se sp|la le lp} eq}
  `{Has_Leibniz@{sa se se|la le le} eq}
  `{Has_refl@{sa se|la le} eq}
  (x:A) (P:A -> Type@{sp|lp}) :
  P x -> forall y:A, eq A y x -> P y.
Proof. compute. intros. eapply (leibniz eq); eauto. eapply eq_sym; eauto. Defined.

Register eq_elim_r as core.eq.poly_r.

Instance eq_Has_Leibniz_r_elim@{s se|l l'|} : Has_Leibniz_r@{s se se|l l l'} (@eq) :=
  fun A x P p y e => eq_elim A x (fun y _ => P y) p y
      (@eq_sym _ (eq_Has_Leibniz_elim@{s se|l l}) _ _ _ _ e).

(*
  Definition eq_rect_r@{α β|u v ? | ? } (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{α Type|_} y x -> P y := fun px y e => eq_elim_r@{α Type β| u u v} _ _ _ px _ e.
*)

Definition eq_rect_r@{α β | u v |} A x P px y e :=
  @eq_elim_r@{α Type β | u u v} (@eq) A
    (* eq_Has_LeibnizType *)
    (fun A x P Px y e => eq_Has_LeibnizType A x P Px y e)
    (fun A x P Px y e => eq_Has_LeibnizType A x P Px y e) eq_Has_refl x P px y e.

Register eq_rect_r as core.eq.rect_r.

Definition eq_singleton_r@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, y = x -> P y :=
  fun px y e =>
    match e in _ = x return P x -> P y with
    | eq_refl => fun py => py
    end px.

Register eq_singleton_r as core.eq.ind_r.

Instance eq_Has_Leibniz_r_Singleton@{s sp|l lp|} : Has_Leibniz_r@{s Prop sp|l 0 lp} (@eq) :=
  eq_singleton_r@{s sp|l lp}.

Definition eq_ind_r@{α|u|} := eq_singleton_r@{α Prop | u 0}.


Definition eq_elim_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{_ β |_} x y -> P y :=
  fun px y e =>
    match e in _ = y return P x -> P y with
    | eq_refl => fun px => px
    end px.

Register eq_elim_d as core.eq.poly.

Definition eq_rect_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, eq@{α Type|_} x y -> P y :=
  fun px y e =>
  match e in _ = y return P x -> P y with
  | eq_refl => fun py => py
  end px.

Register eq_rect_d as core.eq.rect.

Definition eq_ind_d@{α β|u v|} (A:Type@{α|u}) (x:A) (P:A -> Type@{β|v}) :
  P x -> forall y:A, x = y -> P y := eq_singleton (fun y _ => P y).

Register eq_ind_d as core.eq.ind.

Definition f_equal@{s s' e|u v |} {A : Type@{s|u}} {B : Type@{s'|v}} (f : A -> B) {x y} : eq@{_ e| _} x y -> eq@{_ e| _} (f x) (f y)
  := ap@{s e s' e|u u v v} (_leibniz := fun A x P Px y e => eq_Has_Leibniz_elim A x P Px y e) f.

Register f_equal as core.eq.congr.

Arguments f_equal [_ _] _ [_ _] _.

Notation congr := ap.

Definition f_equal2@{s1 s2 s' e|u1 u2 v|}
  {A1 : Type@{s1|u1}}
  {A2 : Type@{s2|u2}}
  {B : Type@{s'|v}}
  (f:A1 -> A2 -> B)
  {x1 y1:A1} {x2 y2:A2} :
  eq@{_ e|_} x1 y1 ->
  eq@{_ e|_} x2 y2 ->
  eq@{_ e|_} (f x1 x2) (f y1 y2) :=
  fun e1 => match e1 with | eq_refl => fun e2 => match e2 with | eq_refl => eq_refl end end.

Register f_equal2 as core.eq.congr2.

Arguments f_equal2 [_ _ _] _ [_ _ _ _] _ _.

Module EqNotations.
  Notation "'rew' H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  H  in  '/' H' ']'").
  Notation "'rew' [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' <- H 'in' H'" := (eq_rect_r _ H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  H  in  '/' H' ']'").
  Notation "'rew' <- [ P ] H 'in' H'" := (eq_rect_r P H' H)
    (at level 10, H' at level 10,
     format "'[' 'rew'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' -> H 'in' H'" := (eq_rect _ _ H' _ H)
    (at level 10, H' at level 10, only parsing).
  Notation "'rew' -> [ P ] H 'in' H'" := (eq_rect _ P H' _ H)
    (at level 10, H' at level 10, only parsing).

  Notation "'rew' 'dependent' H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> H 'in' H'"
    := (match H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, only parsing).
  Notation "'rew' 'dependent' <- H 'in' H'"
    := (match eq_sym H with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ 'fun' y p => P ] H 'in' H'"
    := (match H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name, only parsing).
  Notation "'rew' 'dependent' <- [ 'fun' y p => P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10, y name, p name,
          format "'[' 'rew'  'dependent'  <-  [ 'fun'  y  p  =>  P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  [ P ]  '/    ' H  in  '/' H' ']'").
  Notation "'rew' 'dependent' -> [ P ] H 'in' H'"
    := (match H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          only parsing).
  Notation "'rew' 'dependent' <- [ P ] H 'in' H'"
    := (match eq_sym H as p in (_ = y) return P y p with
        | eq_refl => H'
        end)
         (at level 10, H' at level 10,
          format "'[' 'rew'  'dependent'  <-  [ P ]  '/    ' H  in  '/' H' ']'").
End EqNotations.
