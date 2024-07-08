(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Typeclass-based morphism definition and standard, minimal instances

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Export Coq.Classes.RelationClasses.

Generalizable Variables A eqA B C D R RA RB RC m f x y.
Local Obligation Tactic := try solve [ simpl_relation ].

Local Arguments transitivity {A R Transitive x} y {z}.

Set Universe Polymorphism.

(** * Morphisms.

   We now turn to the definition of [Proper] and declare standard instances.
   These will be used by the [setoid_rewrite] tactic later. *)

(** A morphism for a relation [R] is a proper element of the relation.
   The relation [R] will be instantiated by [respectful] and [A] by an arrow
   type for usual morphisms. *)

Section Proper.
  Sort s s'.
  Universe u v.
  Context {A : Type@{s|u}}.

  Class Proper (R : relation@{s s'|u v} A) (m : A) :=
    proper_prf : R m m.

  (** Every element in the carrier of a reflexive relation is a morphism
   for this relation.  We use a proxy class for this case which is used
   internally to discharge reflexivity constraints.  The [Reflexive]
   instance will almost always be used, but it won't apply in general to
   any kind of [Proper (A -> B) _ _] goal, making proof-search much
   slower. A cleaner solution would be to be able to set different
   priorities in different hint bases and select a particular hint
   database for resolution of a type class constraint. *)

  Class ProperProxy (R : relation@{s s'|u v} A) (m : A) :=
    proper_proxy : R m m.

  Class ReflexiveProxy (R : relation@{s s'|u v} A) :=
    reflexive_proxy : forall x, R x x.

  (** Every reflexive relation gives rise to a morphism.
    If the relation is not determined (is an evar),
    then we restrict the solutions to predefined ones (equality, or iff on Prop),
    using ground instances. If the relation is determined then
    [ReflexiveProxy] calls back to [Reflexive]. *)

  Lemma reflexive_proper `{ReflexiveProxy@{} R} (x : A) : Proper R x.
  Proof. firstorder. Qed.

  Lemma reflexive_proper_proxy `(ReflexiveProxy R) (x : A) : ProperProxy R x.
  Proof. firstorder. Qed.

  Lemma proper_proper_proxy x `(Proper R x) : ProperProxy R x.
  Proof. firstorder. Qed.

  Lemma reflexive_reflexive_proxy `(Reflexive A R) : ReflexiveProxy R.
  Proof. firstorder. Qed.
End Proper.

Section Proper2.
  Sort s s'.
  Universe u.
  Context {A : Type@{s|u}}.
  Lemma eq_proper_proxy (x : A) : ProperProxy (@eq@{s s'|u} A) x.
  Proof. firstorder. Qed.
End Proper2.


(** Respectful morphisms. *)
(** Non-dependent pointwise lifting *)
Definition pointwise_relation@{sa sb srb|a b rb|} {A : Type@{sa|a}} {B : Type@{sb|b}}
  (R : relation@{sb srb|b rb} B) : relation (A -> B) :=
  fun f g => forall a, R (f a) (g a).

(** We let Coq infer these relations when a default relation should
  be found on the function space. *)
Lemma rewrite_relation_pointwise@{sa sb srb|a b rb|} {A : Type@{sa|a}} {B : Type@{sb|b}} {R : relation@{sb srb|b rb} B} `{RewriteRelation B R}:
  RewriteRelation (@pointwise_relation A B R).
Proof. split. Qed.

(** The non-dependent version is an instance where we forget dependencies. *)
Definition respectful@{sa sb sra srb|a b ra rb|} {A : Type@{sa|a}} {B : Type@{sb|b}}
  (R : relation@{sa sra|a ra} A) (R' : relation@{sb srb|b rb} B)
  : relation@{sb srb|_ _} (A -> B) :=
  fun f g => forall x y, R x y -> R' (f x) (g y).

Lemma rewrite_relation_eq_dom@{sa sb sr se|a b r|} {A : Type@{sa|a}} {B : Type@{sb|b}} {R : relation@{sb sr|b r} B} {_ : RewriteRelation R}:
  RewriteRelation@{sb sr|max(a,b) max(a,r)} (respectful (@eq@{sa se|a} A) R).
Proof. split. Qed.

(** Pointwise reflexive *)

Ltac rewrite_relation_fun :=
  (* If we're looking for a default rewrite relation on a
    function type, we favor pointwise equality *)
  class_apply @rewrite_relation_pointwise ||
  (* The relation might be already determined to be (eq ==> _) instead of a
    pointwise equality, but we want to treat them the same. No point in
    backtracking on the previous instance though *)
  class_apply @rewrite_relation_eq_dom.

Global Hint Extern 2 (@RewriteRelation (_ -> _) _) =>
  rewrite_relation_fun : typeclass_instances.

Lemma eq_rewrite_relation@{sa se|a|} {A : Type@{sa|a}} : RewriteRelation (@eq@{sa se|a} A).
Proof. split. Qed.

Ltac eq_rewrite_relation A :=
  solve [unshelve class_apply @eq_rewrite_relation].

Global Hint Extern 100 (@RewriteRelation ?A _) => eq_rewrite_relation A : typeclass_instances.


(** We favor the use of Leibniz equality or a declared reflexive relation
  when resolving [ProperProxy], otherwise, if the relation is given (not an evar),
  we fall back to [Proper]. *)
#[global]
Hint Extern 1 (ProperProxy _ _) =>
  class_apply @eq_proper_proxy || class_apply @reflexive_proper_proxy : typeclass_instances.

#[global]
Hint Extern 2 (ProperProxy ?R _) =>
  not_evar R; class_apply @proper_proper_proxy : typeclass_instances.

(* This tactics takes a type and (partially defined) relation and tries
   to find all instances matching it which completely determine the relation,
   feeding them to kont. *)
Ltac find_rewrite_relation A R kont :=
  assert (@RewriteRelation A R); [solve [unshelve typeclasses eauto]|]; kont R.

(** This hint helps infer "generic" reflexive relations, based only on the type of the
    carrier, when the relation is only partially defined (contains evars). *)

Ltac reflexive_proxy_tac A R :=
  tryif has_evar R then
    (* If the user declared a specific rewrite relation on the type, we favor it.
      By default, [iff] and and [impl] are favored for Prop,
      pointwise equality for function types and finally leibniz equality. *)
    find_rewrite_relation A R ltac:(fun RA =>
      class_apply (@reflexive_reflexive_proxy A RA))
      (* The [Reflexive] subgoal produced here will need no backtracking,
          being a Prop goal without existential variables,
          but we don't have `cut` to explicitely say it. *)
  else
    (* If the relation is determined then we look for a relexivity proof on it *)
    class_apply @reflexive_reflexive_proxy.

#[global]
Hint Extern 1 (@ReflexiveProxy ?A ?R) => reflexive_proxy_tac A R : typeclass_instances.


Declare Scope signature_scope.
Delimit Scope signature_scope with signature.

Module ProperNotations.

  Notation " R ++> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R ==> R' " := (@respectful _ _ (R%signature) (R'%signature))
    (right associativity, at level 55) : signature_scope.

  Notation " R --> R' " := (@respectful _ _ (flip (R%signature)) (R'%signature))
    (right associativity, at level 55) : signature_scope.

End ProperNotations.

Arguments Proper {A}%_type R%_signature m.
Arguments respectful {A B}%_type (R R')%_signature _ _.

Export ProperNotations.

Local Open Scope signature_scope.

(** [solve_proper] try to solve the goal [Proper (?==> ... ==>?) f]
    by repeated introductions and setoid rewrites. It should work
    fine when [f] is a combination of already known morphisms and
    quantifiers. *)

Ltac solve_respectful t :=
 match goal with
   | |- respectful _ _ _ _ =>
     let H := fresh "H" in
     intros ? ? H; solve_respectful ltac:(setoid_rewrite H; t)
   | _ => t; reflexivity
 end.

Ltac solve_proper := unfold Proper; solve_respectful ltac:(idtac).

(** [f_equiv] is a clone of [f_equal] that handles setoid equivalences.
    For example, if we know that [f] is a morphism for [E1==>E2==>E],
    then the goal [E (f x y) (f x' y')] will be transformed by [f_equiv]
    into the subgoals [E1 x x'] and [E2 y y'].
*)

Ltac f_equiv :=
 match goal with
  | |- ?R (?f ?x) (?f' _) =>
    let T := type of x in
    let Rx := fresh "R" in
    evar (Rx : relation T);
    let H := fresh in
    assert (H : (Rx==>R)%signature f f');
    unfold Rx in *; clear Rx; [ f_equiv | apply H; clear H; try reflexivity ]
  | |- ?R ?f ?f' =>
    solve [change (Proper R f); eauto with typeclass_instances | reflexivity ]
  | _ => idtac
 end.

Section Relations.
  Sort s.
  Universes a.
  Context {A : Type@{s|a}}.

  (** Dependent pointwise lifting of a relation on the range. *)

  Definition all_relation@{sr|r|} (P : A -> Type@{s|a})
             (sig : forall a, relation@{s sr|a r} (P a)) : relation@{s sr|a max(a,r)} (forall x, P x) :=
    fun f g => forall a, sig a (f a) (g a).

  Lemma pointwise_pointwise@{s' sb|r b|} {B : Type@{sb|b}} (R : relation@{sb s'|b r} B) :
    relation_equivalence@{sb s'|max(a,b) max(a,r)} (pointwise_relation@{_ _ _|a b r} R)
    (respectful@{_ _ _ _|a b a r} (@eq@{_ s'|a} A) R).
  Proof.
    intros. split.
    - intros X a b []. apply X.
    - firstorder.
  Qed.

  Lemma pointwise_pointwise_prop@{s' sb|r b|} {B : Type@{sb|b}} (R : relation@{sb s'|b r} B) :
    relation_equivalence@{sb s'|max(a,b) max(a,r)} (pointwise_relation@{_ _ _|a b r} R)
    (respectful@{_ _ _ _|a b Set r} (@eq@{_ Prop|a} A) R).
  Proof.
    intros. split.
    - intros X a b []. apply X.
    - firstorder.
  Qed.

  (** Subrelations induce a morphism on the identity. *)

  Global Instance subrelation_id_proper@{s'|b|} `(subrelation@{s s'|a b} A RA RA') : Proper (RA ==> RA') id.
  Proof. firstorder. Qed.

  (** The subrelation property goes through products as usual. *)

  Lemma subrelation_respectful@{s' s2 s2' s3 s3'| b ra rb|?} {B : Type@{s2|b}}
    (RA : relation@{s s'|a ra} A) (RA' : relation@{s s'|a ra} A)
    (RB : relation@{s2 s2'|b rb} B) (RB' : relation@{s2 s2'|b rb} B)
    (subl : subrelation@{s s'|a ra} RA' RA)
    (subr : subrelation@{s2 s2'|b rb} RB RB') :
    subrelation@{s2 s2'|max(a,b) max(a,ra,rb)} (RA ==> RB) (RA' ==> RB').
  Proof. intros f g rfg x y rxy. apply subr, rfg, subl, rxy. Qed.

  (** And of course it is reflexive. *)

  Lemma subrelation_refl@{sr|r|} R : @subrelation@{s sr|a r} A R R.
  Proof. simpl_relation. Qed.

  (** [Proper] is itself a covariant morphism for [subrelation].
   We use an unconvertible premise to avoid looping.
   *)

  Lemma subrelation_proper@{sr'|r'|} (R' : relation@{s sr'|a r'} A) (m : A) (mor : Proper R' m)
        `(unc : Unconvertible (relation A) R R')
        `(sub : subrelation A R' R) : Proper R m.
  Proof.
    intros. apply sub. apply mor.
  Qed.

  Global Instance proper_subrelation_proper_arrow :
    Proper (subrelation ++> eq ==> arrow) (@Proper A).
  Proof. reduce. destruct X0. firstorder. Qed.

  Global Instance pointwise_subrelation@{sb sr'|b r'|} {B : Type@{sb|b}} (R R' : relation@{sb sr'|b r'} B) (sub : subrelation R R') :
    subrelation@{_ _|max(a,b) max(a,r')} (@pointwise_relation A B R) (pointwise_relation R') | 4.
  Proof. reduce. unfold pointwise_relation in *. apply sub. auto. Qed.

  (** For dependent function types. *)
  Lemma all_subrelation@{sr|r|} (P : A -> Type@{s | a}) (R : forall x : A, relation@{s sr|a r} (P x)) (S : forall x : A, relation@{s sr|a r} (P x)) :
    (forall a, subrelation (R a) (S a)) ->
    subrelation (all_relation P R) (all_relation P S).
  Proof. reduce. firstorder. Qed.
End Relations.
Global Typeclasses Opaque respectful pointwise_relation all_relation.
Arguments all_relation {A P}%_type sig%_signature _ _.
Arguments pointwise_relation A%_type {B}%_type R%_signature _ _.

#[global]
Hint Unfold Reflexive : core.
#[global]
Hint Unfold Symmetric : core.
#[global]
Hint Unfold Transitive : core.

(** Resolution with subrelation: favor decomposing products over applying reflexivity
  for unconstrained goals. *)
Ltac subrelation_tac T U :=
  (is_ground T ; is_ground U ; class_apply @subrelation_refl) ||
    class_apply @subrelation_respectful || class_apply @subrelation_refl.

#[global]
Hint Extern 3 (@subrelation _ ?T ?U) => subrelation_tac T U : typeclass_instances.

CoInductive apply_subrelation : Prop := do_subrelation.

Ltac proper_subrelation :=
  match goal with
    [ H : apply_subrelation |- _ ] => clear H ; class_apply @subrelation_proper
  end.

#[global]
Hint Extern 5 (@Proper _ ?H _) => proper_subrelation : typeclass_instances.

(** Essential subrelation instances for [iff], [arrow] and [pointwise_relation]. *)

#[global]
Instance iff_arrow_subrelation@{s | u|} : subrelation iff@{s|u u} arrow@{s s|u u} | 2.
Proof. Show Universes. firstorder.  Qed.

#[global]
Instance iff_flip_arrow_subrelation@{s | u|} : subrelation iff@{s|u u} (flip arrow@{s s|u u}) | 2.
Proof. firstorder. Qed.


(** We use an extern hint to help unification. *)

#[global]
Hint Extern 4 (subrelation (@all_relation ?A ?B ?R) (@all_relation _ _ ?S)) =>
  apply (@all_subrelation A B R S) ; intro : typeclass_instances.

Section GenericInstances.
  (* Share universes *)
  Sort sa sra.
  Universe a ra.
  Context (A : Type@{sa | a}) (R : relation@{sa sra | a ra} A).

  (** Every Transitive relation gives rise to a binary morphism on [arrow],
   contravariant in the first argument, covariant in the second. *)

  Global Program
  Instance trans_contra_co_type_morphism
    `(Transitive A R) : Proper (R --> R ++> arrow) R.

  Next Obligation.
  Proof with auto.
    intros H x y X x0 y0 X0 X1.
    apply transitivity with x...
    apply transitivity with x0...
  Qed.

  (** Proper declarations for partial applications. *)

  Global Program
  Instance trans_contra_inv_arrow_type_morphism
  `(Transitive A R) {x} : Proper (R --> flip arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros H x x0 y X X0.
    apply transitivity with y...
  Qed.

  Global Program
  Instance trans_co_arrow_type_morphism
    `(Transitive A R) {x} : Proper (R ++> arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros H x x0 y X X0.
    apply transitivity with x0...
  Qed.

  Global Program
  Instance trans_sym_co_inv_arrow_type_morphism
    `(PER A R) {x} : Proper (R ++> flip arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros H x x0 y X X0.
    apply transitivity with y... apply symmetry...
  Qed.

  Global Program Instance trans_sym_contra_arrow_morphism
    `(PER A R) {x} : Proper (R --> arrow) (R x) | 3.

  Next Obligation.
  Proof with auto.
    intros H x x0 y X X0.
    apply transitivity with x0... apply symmetry...
  Qed.

  Global Program Instance per_partial_app_type_morphism
  `(PER A R) {x} : Proper (R ==> iff) (R x) | 2.

  Next Obligation.
  Proof with auto.
    intros H x x0 y X.
    split.
    - intros ; apply transitivity with x0...
    - intros.
      apply transitivity with y...
      apply symmetry...
  Qed.

  (** Every Transitive relation induces a morphism by "pushing" an [R x y] on the left of an [R x z] proof to get an [R y z] goal. *)

  Global Program
  Instance trans_co_eq_inv_arrow_morphism@{| |}
  (_ : Transitive R) : Proper (R ==> (@eq@{sa sra|a} A) ==> flip (C := Type@{sra|ra}) arrow) R | 2.

  Next Obligation.
  Proof with auto.
    intros H x y X y0 y1 e X0; destruct e.
    apply transitivity with y...
  Qed.

  (** Every Symmetric and Transitive relation gives rise to an equivariant morphism. *)

  Global Program
  Instance PER_type_morphism `(PER A R) : Proper (R ==> R ==> iff) R | 1.

  Next Obligation.
  Proof with auto.
    intros H x y X x0 y0 X0.
    split ; intros.
    - apply transitivity with x0...
      apply transitivity with x... apply symmetry...

    - apply transitivity with y... apply transitivity with y0...
      apply symmetry...
  Qed.

  Lemma symmetric_equiv_flip@{} (HS : Symmetric R) :
    relation_equivalence R (flip (C:=Type@{sra | _}) R).
  Proof. red. unfold flip. intros x y; split; apply symmetry. Qed.

  (** We can build a PER on the Coq function space if we have PERs on the domain and
   codomain. *)

  Program Instance respectful_per@{sb srb | b rb |} (pera : PER R) {B} {R' : relation@{sb srb | b rb} B}
   (perb : PER R') : PER (R ==> R').

  Next Obligation.
  Proof with auto.
    intros pera B R' perb x y z X X0 x0 y0 X1.
    assert(R x0 x0).
    - eapply transitivity with y0... apply symmetry. exact X1.
    - eapply transitivity with (y x0)...
  Qed.

 Unset Strict Universe Declaration.

 (** The complement of a relation conserves its proper elements. *)

 (** The [flip] too, actually the [flip] instance is a bit more general. *)
 Program Definition flip_proper@{sb srb sc src | b rb c rc |}
  {B} {RB : relation@{sb srb | b rb} B}
  {C} {RC : relation@{sc src | c rc} C}
  (f : A -> B -> C)
  (mor : Proper (R ==> RB ==> RC) f) :
   Proper (RB ==> R ==> RC) (flip f) := _.

 Next Obligation.
 Proof.
   intros B RB C RC f mor x y X x0 y0 X0.
   apply mor ; auto.
 Qed.



  Global Program Instance compose_proper@{sb srb sc src | b rb c rc |}
  {B} {RB : relation@{sb srb | b rb} B}
  {C} {RC : relation@{sc src | c rc} C} :
  Proper ((RB ==> RC) ==> ((R ==> RB) ==> (R ==> RC))) (@compose A B C).

  Next Obligation.
  Proof.
    simpl_relation.
    unfold compose. apply X, X0, X1.
  Qed.

  (** Coq functions are morphisms for Leibniz equality,
     applied only if really needed. *)

    (** [respectful] is a morphism for relation equivalence . *)
  Global Instance respectful_morphism@{sb srb | b rb |} {B : Type@{sb | b}} :
    Proper (relation_equivalence@{sa sra | a ra} ++>
            relation_equivalence@{sb srb | b rb} ++> relation_equivalence)
           (@respectful A B).
  Proof.
    intros R0 R0' HRR' S S' HSS' f g.
    unfold respectful , relation_equivalence in *; simpl in *.
    split ; intros H x y Hxy.
    - apply (fst (HSS' _ _)), H, (snd (HRR' _ _)), Hxy.
    - apply (snd (HSS' _ _)), H, (fst (HRR' _ _)), Hxy.
  Qed.

  (** [R] is Reflexive, hence we can build the needed proof. *)

  Lemma Reflexive_partial_app_morphism@{sb srb | b rb |}
    {B} {RB : relation@{sb srb | b rb} B}
    {m : A -> B}
    (pm : Proper (R ==> RB) m) {x} (pr : ProperProxy R x) :
    Proper@{sb srb | b rb} RB (m x).
  Proof. simpl_relation. Qed.

  #[projections(primitive=no)]
  Class Params {A} (of : A) (arity : nat) := {}.

  Lemma flip_respectful@{sb srb | b rb| ?}
    {B} {RB : relation@{sb srb | b rb} B} :
    relation_equivalence@{sb srb | max(a,b) max(a, ra, rb)}
    (flip (C:=Type@{srb | max(a, ra, rb)}) (R ==> RB)) (flip (C:=Type@{sra | ra}) R ==> flip (C:=Type@{srb | rb}) RB).
  Proof.
    intros.
    unfold flip, respectful.
    split ; intros ; intuition.
  Qed.


  (** Treating flip: can't make them direct instances as we
   need at least a [flip] present in the goal. *)

  Lemma flip1 `(subrelation A R' R) : subrelation (flip (C:=Type@{sra | ra}) (flip (C:=Type@{sra | ra}) R')) R.
  Proof. firstorder. Qed.

  Lemma flip2 `(subrelation A R R') : subrelation R (flip (C:=Type@{sra | ra}) (flip (C:=Type@{sra | ra}) R')).
  Proof. firstorder. Qed.

  (** That's if and only if *)

  Lemma eq_subrelation `(Reflexive A R) : subrelation (@eq@{sa sra | a} A) R.
  Proof. simpl_relation. Qed.

  (** Once we have normalized, we will apply this instance to simplify the problem. *)

  Definition proper_flip_proper `(mor : Proper A R m) : Proper (flip R) m := mor.

End GenericInstances.


Global Instance reflexive_eq_dom_reflexive@{sa sb sr | a b r |}
  {A : Type@{sa|a}} {B : Type@{sb|b}} {RB : relation@{sb sr | b r} B}
  (hr : Reflexive RB) :
  Reflexive (@eq@{_ sr|a} A ==> RB).
Proof. simpl_relation. Qed.

Lemma proper_eq@{s | a |} {A : Type@{s | a}} (x : A) : Proper (@eq@{_ _|a} A) x.
Proof. intros. apply reflexive_proper. Qed.

#[projections(primitive=no)]
Class PartialApplication.

CoInductive normalization_done : Prop := did_normalization.

Ltac partial_application_tactic :=
  let rec do_partial_apps H m cont :=
    match m with
      | ?m' ?x => class_apply @Reflexive_partial_app_morphism ;
        [(do_partial_apps H m' ltac:(idtac))|clear H]
      | _ => cont
    end
  in
  let rec do_partial H ar m :=
    match ar with
      | O => do_partial_apps H m ltac:(fail 1)
      | S ?n' =>
        match m with
          ?m' ?x => do_partial H n' m'
        end
    end
  in
  let params m sk fk :=
    (let m' := fresh in head_of_constr m' m ;
     let n := fresh in evar (n:nat) ;
     let v := eval compute in n in clear n ;
      let H := fresh in
        assert(H:Params m' v) by typeclasses eauto ;
          let v' := eval compute in v in subst m';
            (sk H v' || fail 1))
    || fk
  in
  let on_morphism m cont :=
    params m ltac:(fun H n => do_partial H n m)
      ltac:(cont)
  in
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : @Params _ _ _ |- _ ] => fail 1
    | [ |- @Proper ?T _ (?m ?x) ] =>
      match goal with
        | [ H : PartialApplication |- _ ] =>
          class_apply @Reflexive_partial_app_morphism; [|clear H]
        | _ => on_morphism (m x)
          ltac:(class_apply @Reflexive_partial_app_morphism)
      end
  end.

(** Bootstrap !!! *)

#[global]
Instance proper_proper {A} : Proper (relation_equivalence ==> eq ==> iff) (@Proper A).
Proof.
  intros R R' HRR' x y eq; destruct eq. red in HRR'.
  split ; red ; intros X.
  - apply (fst (HRR' _ _)), X.
  - apply (snd (HRR' _ _)), X.
Qed.

Ltac proper_reflexive :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | _ => class_apply proper_eq || class_apply @reflexive_proper
  end.


#[global]
Hint Extern 1 (subrelation (flip _) _) => class_apply @flip1 : typeclass_instances.
#[global]
Hint Extern 1 (subrelation _ (flip _)) => class_apply @flip2 : typeclass_instances.

(* Hint Extern 1 (Proper _ (complement _)) => apply @complement_proper  *)
(*   : typeclass_instances. *)
#[global]
Hint Extern 1 (Proper _ (flip _)) => apply @flip_proper
  : typeclass_instances.
#[global]
Hint Extern 2 (@Proper _ (flip _) _) => class_apply @proper_flip_proper
  : typeclass_instances.
#[global]
Hint Extern 4 (@Proper _ _ _) => partial_application_tactic
  : typeclass_instances.
#[global]
Hint Extern 7 (@Proper _ _ _) => proper_reflexive
  : typeclass_instances.

(** Special-purpose class to do normalization of signatures w.r.t. flip. *)

Section Normalize.
  Sort s. Universe u.
  Context (A : Type@{s | u}).

  Class Normalizes@{s' | v |} (m : relation@{s s' | u v} A) (m' : relation A) :=
    normalizes : relation_equivalence m m'.

  (** Current strategy: add [flip] everywhere and reduce using [subrelation]
   afterwards. *)

  Lemma proper_normalizes_proper `(Normalizes R0 R1, Proper A R1 m) : Proper R0 m.
  Proof.
    apply (_ : Normalizes R0 R1). assumption.
  Qed.

  Lemma flip_atom@{s' | v |} (R : relation@{s s'| u v} A)  : Normalizes R (flip (flip R)).
  Proof.
    do 2 red. intros x y; unfold flip; split; firstorder.
  Qed.

End Normalize.

Lemma flip_arrow `(NA : Normalizes A R (flip R'''), NB : Normalizes B R' (flip R'')) :
  Normalizes (A -> B) (R ==> R') (flip (R''' ==> R'')%signature).
Proof.
  unfold Normalizes in *. intros.
  eapply transitivity; [|eapply symmetry, flip_respectful].
  apply respectful_morphism, NB.
  apply NA.
Qed.

Ltac normalizes :=
  match goal with
    | [ |- Normalizes _ (respectful _ _) _ ] => class_apply @flip_arrow
    | _ => class_apply @flip_atom
  end.

Ltac proper_normalization :=
  match goal with
    | [ _ : normalization_done |- _ ] => fail 1
    | [ _ : apply_subrelation |- @Proper _ ?R _ ] =>
      let H := fresh "H" in
      set(H:=did_normalization) ; class_apply @proper_normalizes_proper
  end.

#[global]
Hint Extern 1 (Normalizes _ _ _) => normalizes : typeclass_instances.
#[global]
Hint Extern 6 (@Proper _ _ _) => proper_normalization
  : typeclass_instances.

(** When the relation on the domain is symmetric, we can
flip the relation on the codomain. Same for binary functions. *)

Lemma proper_sym_flip :
forall `(Symmetric A R1)`(Proper (A->B) (R1==>R2) f),
Proper (R1==>flip R2) f.
Proof.
intros A R1 Sym B R2 f Hf.
intros x x' Hxx'. apply Hf, Sym, Hxx'.
Qed.

Lemma proper_sym_flip_2 :
forall `(Symmetric A R1)`(Symmetric B R2)`(Proper (A->B->C) (R1==>R2==>R3) f),
Proper (R1==>R2==>flip R3) f.
Proof.
intros A R1 Sym1 B R2 Sym2 C R3 f Hf.
intros x x' Hxx' y y' Hyy'. apply Hf; auto.
Qed.

(** When the relation on the domain is symmetric, a predicate is
    compatible with [iff] as soon as it is compatible with [arrow].
    Same with a binary relation. *)

Lemma proper_sym_arrow_iff@{sa sra sf|a ra f|} : forall {A : Type@{sa|a}} {R : relation@{sa sra|a ra} A} {f : A -> Type@{sf|f}},
  Symmetric R -> Proper (R==>arrow) f ->
  Proper (R==>iff) f.
Proof.
intros A R Sym f Hf x x' Hxx'. repeat red in Hf. split; eauto.
Qed.

Lemma proper_sym_arrow_iff_2@{sa sra sb srb sf|a ra b rb f|} :
forall {A : Type@{sa|a}} {B : Type@{sb|b}} {R : relation@{sa sra|a ra} A} {R' : relation@{sb srb|b rb} B} {f : A -> B -> Type@{sf|f}}, (Symmetric R) -> (Symmetric R') -> (Proper (R==>R'==>arrow) f) ->
Proper (R==>R'==>iff) f.
Proof.
intros A R Sym B R' Sym' f Hf x x' Hxx' y y' Hyy'.
repeat red in Hf. split; eauto.
Qed.

(** A [PartialOrder] is compatible with its underlying equivalence. *)
(* Require Import Relation_Definitions. *)

#[global]
Instance PartialOrder_proper_type@{s s'|u v|} {A : Type@{s | u}} (eqA : relation@{s s' | u v} A) {isEq : Equivalence eqA}
  (R : relation@{s s' | u v} A) {isPreOrder : PreOrder R} (_ : PartialOrder eqA R) :
    Proper (eqA==>eqA==>iff) R.
Proof.
intros.
apply proper_sym_arrow_iff_2. 1-2: typeclasses eauto.
intros x x' Hx y y' Hy Hr.
apply transitivity with x.
- apply X, symmetry, Hx.
- apply transitivity with y; auto. apply X, Hy.
Qed.

(** From a [PartialOrder] to the corresponding [StrictOrder]:
    [lt = le /\ ~eq].
    If the order is total, we could also say [gt = ~le]. *)

Lemma PartialOrder_StrictOrder `(PartialOrder A eqA R) :
    StrictOrder (relation_conjunction R (complement eqA)).
Proof.
split; compute.
- intros x (_,Hx). apply Hx, Equivalence_Reflexive.
- intros x y z (Hxy,Hxy') (Hyz,Hyz'). split.
    + apply PreOrder_Transitive with y; assumption.
    + intro Hxz.
    apply Hxy'.
    apply partial_order_antisym; auto.
    apply transitivity with z; [assumption|].
    now apply H.
Qed.

(** From a [StrictOrder] to the corresponding [PartialOrder]:
    [le = lt \/ eq].
    If the order is total, we could also say [ge = ~lt]. *)

Lemma StrictOrder_PreOrder
  `(Equivalence A eqA, StrictOrder A R,Proper _ (eqA==>eqA==>iff) R) :
  PreOrder (relation_disjunction R eqA).
Proof.
split.
- intros x. right. apply reflexivity.
- intros x y z [Hxy|Hxy] [Hyz|Hyz].
  + left. apply transitivity with y; auto.
  + left. eapply H1; try eassumption. apply reflexivity.
  + left. eapply H1 with y z; [apply symmetry, Hxy|apply reflexivity|try eassumption].
  + right. apply transitivity with y; auto.
Qed.

#[global]
Hint Extern 4 (PreOrder (relation_disjunction _ _)) =>
    class_apply StrictOrder_PreOrder : typeclass_instances.

Lemma StrictOrder_PartialOrder
    `(Equivalence A eqA, StrictOrder A R, H1 : Proper _ (eqA==>eqA==>iff) R) :
    @PartialOrder _ eqA _ (relation_disjunction R eqA) (StrictOrder_PreOrder _ _ H1).
Proof.
intros. intros x y. split.
- intros heq. split. right; apply heq.
  unfold flip. right; apply symmetry, heq.
- unfold flip. intros [[l|l] [r|r]].
  * destruct (StrictOrder_Irreflexive x (transitivity _ l r)).
  * eapply symmetry, r.
  * eapply l.
  * eapply l.
Qed.

#[global]
Hint Extern 4 (StrictOrder (relation_conjunction _ _)) =>
    class_apply PartialOrder_StrictOrder : typeclass_instances.

#[global]
Hint Extern 4 (PartialOrder _ (relation_disjunction _ _)) =>
  class_apply StrictOrder_PartialOrder : typeclass_instances.

(* Register bindings for the generalized rewriting tactic *)

Register all_relation as rewrite.type.forall_relation.
Register pointwise_relation as rewrite.type.pointwise_relation.
Register respectful as rewrite.type.respectful.
Register all as rewrite.type.forall_def.
Register do_subrelation as rewrite.type.do_subrelation.
Register apply_subrelation as rewrite.type.apply_subrelation.
Register Proper as rewrite.type.Proper.
Register ProperProxy as rewrite.type.ProperProxy.
