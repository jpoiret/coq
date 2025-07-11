Sort sprop.
Set Universe Polymorphism.
Set Printing Universes.

Module Reduction.

  Definition qsort := 𝒰.
  (* qsort@{α;u |} = 𝒰@{α;u} : 𝒰@{u+1} *)

  Definition qsort' : 𝒰 := 𝒰.
  (* qsort'@{α;u u0 |} = 𝒰@{α;u0} : 𝒰@{u} *)

  Monomorphic Universe U.

  Definition tU := 𝒰@{U}.
  Definition qU := qsort@{Type;U}.

  Definition q1 := Eval lazy in qU.
  Check eq_refl : q1 = tU.

  Definition q2 := Eval vm_compute in qU.
  Check eq_refl : q2 = tU.

  Definition q3 := Eval native_compute in qU.
  Check eq_refl : q3 = tU.

  Definition exfalso (A:𝒰) (H:False) : A := match H with end.
  (* exfalso@{α;u |} : forall A : 𝒰@{α;_}, False -> A *)

  Definition exfalsoVM := Eval vm_compute in exfalso@{Type;Set}.
  Definition exfalsoNative := Eval native_compute in exfalso@{Type;Set}.

  Fixpoint iter@{s;u|Type~>s} (A:𝒰@{s;u}) (f:A -> A) (n : nat) (x : A) : A :=
    match n with
    | 0 => x
    | S k => iter A f k (f x)
    end.
  (* iter@{s;u | s ~> Type} : forall (A : 𝒰@{s;u}) (_ : forall _ : A, A) (_ : nat) (_ : A), A *)

  Definition iterType := Eval lazy in iter@{Type;_}.
  Definition iterSProp := Eval lazy in iter@{SProp;_}.

End Reduction.

Module Conversion.

  Inductive Box (A:𝒰) := box (_:A).
  (* Box@{α α0;u |} (A : 𝒰@{α;u}) : 𝒰@{α0;u} *)


  Definition t1 (A:𝒰) (x y : A) := box _ x.
  (* t1@{α α0;u |} : forall (A : 𝒰@{α;u}) (_ : A) (_ : A), Box@{α α0;u} A *)
  Definition t2 (A:𝒰) (x y : A) := box _ y.
  (* t2@{α α0;u |} : forall (A : 𝒰@{α;u}) (_ : A) (_ : A), Box@{α α0;u} A *)

  Definition t1' (A:𝒰) (x y : A) := x.
  (* t1'@{α;u |} : forall (A : 𝒰@{α;u}) (_ : A) (_ : A), A *)
  Definition t2' (A:𝒰) (x y : A) := y.

  Fail Check eq_refl : t1 nat = t2 nat.
  Fail Check eq_refl : t1' nat = t2' nat.

  Check fun A:SProp => eq_refl : t1 A = t2 A.
  (* : forall A : SProp,
       @eq (forall (_ : A) (_ : A), Box@{SProp Type;sort_poly_elab.475} A)
         (t1@{SProp Type;sort_poly_elab.475} A)
         (t2@{SProp Type;sort_poly_elab.475} A) *)

  Check fun A:SProp => eq_refl : box _ (t1' A) = box _ (t2' A).
  (* : forall A : SProp,
       @eq
         (Box@{SProp Type;sort_poly_elab.479} (forall (_ : A) (_ : A), A))
         (box@{SProp Type;sort_poly_elab.479} (forall (_ : A) (_ : A), A)
            (t1'@{SProp;sort_poly_elab.480} A))
         (box@{SProp Type;sort_poly_elab.479} (forall (_ : A) (_ : A), A)
            (t2'@{SProp;sort_poly_elab.482} A)) *)

  Definition ignore {A:𝒰} (x:A) := tt.
  (* ignore@{α;u |} : forall {A : 𝒰@{α;u}} (_ : A), unit *)

  Definition unfold_ignore (A:𝒰) : ignore (t1 A) = ignore (t2 A) := eq_refl.
  (* unfold_ignore@{α α0 α1;u |} : forall A : 𝒰@{α;u},
       @eq unit
         (@ignore@{α0;u} (forall (_ : A) (_ : A), Box@{α α0;u} A)
            (t1@{α α0;u} A))
         (@ignore@{α1;u} (forall (_ : A) (_ : A), Box@{α α1;u} A)
            (t2@{α α1;u} A)) *)

  Definition t (A:SProp) := Eval lazy in t1 A.
  (* t@{α;u |} : forall (A : SProp) (_ : A) (_ : A), Box@{SProp α;u} A *)

  Axiom v : forall (A:𝒰), bool -> A.
  Fail Check fun P (x:P (v@{Type|_} nat true)) => x : P (v nat false).
  Check fun (A:SProp) P (x:P (v A true)) => x : P (v A false).
    (* : forall (A : SProp) (P : A -> Type@{sort_poly_elab.105}),
       P (v@{SProp;sort_poly_elab.104} A true) ->
       P (v@{SProp;sort_poly_elab.106} A false) *)
End Conversion.

Module Inference.
  Definition zog (A:𝒰) := A.
  (* zog@{α;u |} : 𝒰@{α;_} -> 𝒰@{α;_} *)

  (* implicit instance of zog gets a variable which then gets unified with s from the type of A *)
  Definition zag (A:𝒰) := zog A.
  (* zag@{α;u |} : 𝒰@{α;_} -> 𝒰@{α;_} *)

  (* implicit type of A gets unified to 𝒰@{s|u} *)
  Definition zig A := zog A.
  (* zig@{α;u |} : 𝒰@{α;_} -> 𝒰@{α;_} *)

  (* different manually bound sort variables don't unify *)
  Fail Definition zog'@{s s';u} (A:𝒰@{s;u}) := zog@{s'; u} A.
End Inference.

Module Inductives.
  Inductive foo1 : 𝒰 := .
  (* foo1@{α;u |} : 𝒰@{α;_} :=  . *)
  Check foo1_poly.
  Fail Check foo1_sind.

  Definition foo1_rect@{u1 u2} := foo1_poly@{Type Type|u1 u2}.
  Definition foo1_ind@{u1 u2} := foo1_poly@{Type Prop|u1 u2}.

  (* Fails if constraints cannot be extended *)
  Fail Definition foo1_False@{s|+|} (x : foo1@{s|_}) : False := match x return False with end.
  (* Elimination constraints are not implied by the ones declared: s ~> Prop *)

  Definition foo1_False@{s|+|+} (x : foo1@{s|_}) : False := match x return False with end.
  (* s;u |= s ~> Prop *)

  Definition foo1_False' (x : foo1) : False := match x return False with end.
  (* foo1_False'@{α;u |} : foo1@{α;u} -> False *)
  (* α;u |= α ~> Prop *)

  Inductive foo2 : 𝒰 := Foo2 : 𝒰 -> foo2.
  (* foo2@{α;u |} : 𝒰@{α;u+1} *)
  Fail Check foo2_rect.

  Inductive foo3 (A : 𝒰) : 𝒰 := Foo3 : A -> foo3 A.
  (* foo3@{α α0;u |} (A : 𝒰@{α;u}) : 𝒰@{α0;u} *)
  Fail Check foo3_rect.

  Inductive foo5 (A : 𝒰) : Prop := Foo5 (_ : A).
  (* foo5@{α;u |} (A : 𝒰@{α;u}) : Prop := *)

  Definition foo5_ind' : forall (A : 𝒰) (P : Prop), (A -> P) -> foo5 A -> P
    := foo5_ind.

  Fail Definition foo5_Prop_rect (A:Prop) (P:foo5 A -> 𝒰)
    (H : forall a, P (Foo5 A a))
    (f : foo5 A)
    : P f
    := match f with Foo5 _ a => H a end.
  (* The command has indeed failed with message:
     This expression would enforce an elimination constraint between Prop and
     α96 that is not allowed. *)

  Definition foo5_Prop_rect' (A : Prop) (P : foo5 A -> 𝒰)
    (H : forall a, P (Foo5 A a))
    (f : foo5@{Prop|_} A)
    : P f
    := match f with Foo5 _ a => H a end.

  (* all sort poly output with nonzero contructors are squashed (avoid interfering with uip) *)
  Inductive foo6 : 𝒰 := Foo6.
  Fail Check foo6_sind.

  Definition foo6_rect (P:foo6 -> 𝒰)
    (H : P Foo6)
    (f : foo6)
    : P f
    := match f with Foo6 => H end.

  Definition foo6_prop_rect (P:foo6 -> 𝒰)
    (H : P Foo6)
    (f : foo6@{Prop|_})
    : P f
    := match f with Foo6 => H end.

  Definition foo6_type_rect (P:foo6 -> 𝒰)
    (H : P Foo6)
    (f : foo6@{Type|_})
    : P f
    := match f with Foo6 => H end.

  Inductive foo7 : 𝒰 := Foo7_1 | Foo7_2.
  Fail Check foo7_sind.
  Fail Check foo7_ind.

  Definition foo7_prop_ind (P:foo7 -> Prop)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop|})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Fail Definition foo7_prop_rect (P:foo7 -> 𝒰)
    (H : P Foo7_1) (H' : P Foo7_2)
    (f : foo7@{Prop|})
    : P f
    := match f with Foo7_1 => H | Foo7_2 => H' end.

  Set Primitive Projections.
  Set Warnings "+records".

  (* the SProp instantiation may not be primitive so the whole thing must be nonprimitive *)
  Fail Record R1 : 𝒰 := {}.

  (* the 𝒰 instantiation may fail *)
  (* R2@{Type;} may not be primitive  *)
  Record R2 (A:SProp) : 𝒰 := { R2f1 : A }.

  Goal forall (A:SProp) (r2 : R2@{Type;0} A), r2 = {| R2f1 := r2.(R2f1 A) |}.
  Proof. intros A r2. Fail reflexivity. Abort.

  Goal forall (A:SProp) (r2 : R2@{SProp;0} A), r2 = {| R2f1 := r2.(R2f1 A) |}.
  Proof. intros A r2. reflexivity. Abort.

  (* R3@{SProp Type|} may not be primitive  *)
  Record R3 (A:𝒰) : 𝒰 := { R3f1 : A }.

  Example R3_same_sort@{s;u} (A :𝒰@{s;u}) : forall (r3 : R3@{s s;u} A), r3 = {| R3f1 := r3.(R3f1 A) |}.
  Proof. intros r3. reflexivity. Qed.

  Goal forall (A:SProp) (r3 : R3@{_ Type;0} A), r3 = {| R3f1 := r3.(R3f1 A) |}.
  Proof. intros A r3. Fail reflexivity. Abort.

  Goal forall (A:SProp) (r3 : R3@{_ SProp;0} A), r3 = {| R3f1 := r3.(R3f1 A) |}.
  Proof. intros A r3. reflexivity. Abort.

  (* non SProp instantiation must be squashed *)
  Fail Record R5@{s;u} (A:𝒰@{s;u}) : SProp := { R5f1 : A}. (* FIXME: Universe issues *)
  Fail #[warnings="-non-primitive-record"]
    Record R5 (A:𝒰) : SProp := { R5f1 : A}.
  (* This expression would enforce an elimination constraint between SProp and
  β0 that is not allowed. *)

  Fail #[warnings="-non-primitive-record,-cannot-define-projection"]
    Record R5 (A:𝒰) : SProp := { R5f1 : A}.
  (* This expression would enforce an elimination constraint between SProp and
  β0 that is not allowed. *)

  Record R6@{s;u} (A:𝒰@{s;0}) : 𝒰@{s;0} := { R6f1 : A; R6f2 : nat }.

  Fail Check fun (A:SProp) (x y : R6@{SProp;_} A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:Prop) (x y : R6@{Prop;_} A) =>
          eq_refl : Conversion.box _ x.(R6f1 _) = Conversion.box _ y.(R6f1 _).
  Fail Check fun (A:SProp) (x y : R6@{SProp;_} A) =>
          eq_refl : Conversion.box _ x.(R6f2 _) = Conversion.box _ y.(R6f2 _).

  (* Elimination constraints are accumulated by fields, even on independent fields *)
  #[projections(primitive=no)] Record R7 (A:𝒰) := { R7f1 : A; R7f2 : nat }.
  (* Record R7@{α α0 | u |} (A : 𝒰@{α | u}) : 𝒰@{α0 | max(Set,u)}  *)
  (* R7f1@{α α0 | u |} : forall A : 𝒰@{α | u}, R7@{α α0 | u} A -> A
      α α0 | u |= α0 ~> α *)
  (* R7f2@{α α0 | u |} : forall A : 𝒰@{α | u}, R7@{α α0 | u} A -> nat
      α α0 | u |= α0 ~> α
                  α0 ~> Type *)

  Unset Primitive Projections.

  (* Elimination constraints are accumulated by fields *)
  Record R8 := {
    R8f1 : 𝒰;
    R8f2 : R8f1
  }.
  (* Record R8@{α α0 | u |} : 𝒰@{α | u+1}. *)
  (* R8f1@{α α0 | u |} : R8@{α α0 | u} -> 𝒰@{α0 | u}
      α α0 | u |= α ~> Type *)
  (* R8f2@{α α0 | u |} : forall r : R8@{α α0 | u}, R8f1@{α α0 | u} r
      α α0 | u |= α ~> α0
                  α ~> Type *)

  Inductive sigma (A:𝒰) (B:A -> 𝒰) : 𝒰
    := pair : forall x : A, B x -> sigma A B.
  (* Inductive sigma@{α α0 α1 | u u0 |} (A : 𝒰@{α | u}) (B : A -> 𝒰@{α0 | u0}) : 𝒰@{α1 | max(u,u0)} *)

  (* Elimination constraints are added *)
  Definition pr1 {A B} (s:sigma A B) : A
    := match s with pair _ _ x _ => x end.
  (* α α0 α1 | u u0 |= α1 ~> α *)

  Definition pr2 {A B} (s:sigma A B) : B (pr1 s)
    := match s with pair _ _ _ y => y end.
  (* α α0 α1 | u u0 |= α1 ~> α
                       α1 ~> α0 *)

  Inductive seq (A:𝒰) (a:A) : A -> Prop := seq_refl : seq A a a.
  (* Inductive seq@{α | u |} (A : 𝒰@{α | u}) (a : A) : A -> Prop *)
  Arguments seq_refl {_ _}.

  Definition eta A B (s:sigma A B) : seq _ s (pair A B (pr1 s) (pr2 s)).
  Proof.
    destruct s. simpl. reflexivity.
  Qed.

  Set Primitive Projections.
  Set Warnings "+records".
  (* sigma as a primitive record works better *)
  Record Rsigma (A:𝒰) (B:A -> 𝒰) : 𝒰
    := Rpair { Rpr1 : A; Rpr2 : B Rpr1 }.

  (* match desugared to primitive projections using definitional eta *)
  Fail Definition Rsigma_srect A B
    (P : Rsigma A B -> 𝒰)
    (H : forall x b, P (Rpair _ _ x b))
    (s:Rsigma A B)
    : P s
    := match s with Rpair _ _ x b => H x b end.

  (* sort polymorphic exists (we could also make B sort poly)
     can't be a primitive record since the first projection isn't defined at all sorts *)
  Inductive sexists (A:𝒰) (B:A -> Prop) : Prop
    := sexist : forall a:A, B a -> sexists A B.

  (* we can eliminate to Prop *)
  Check sexists_ind.


  Definition π1 {A:𝒰} {P:A -> 𝒰} (p : sigma@{_ _ Type|_ _} A P) : A :=
    match p return A with pair _ _ a _ => a end.


  (*** List examples *)
  Fixpoint map {A B:𝒰} (f:A -> B) (l:list A) : list B :=
    match l with
    | nil => nil
    | cons x xs => cons (f x) (map f xs)
    end.

  Inductive bool : 𝒰 := true | false.

  Definition andb (b1 b2 : bool) := if b1 then b2 else false.

  Fixpoint allb {A:𝒰} (p:A -> bool) (l:list A) : bool :=
    match l with
    | nil => true
    | cons x xs => andb (p x) (allb p xs)
    end.
  (* allb@{α α0 α1 α2 ; u |} : forall {A : 𝒰@{α ; u}},
       (A -> bool@{α0 ; }) -> list@{α α1 ; u} A -> bool@{α2 ; }
(* α α0 α1 α2 | α0 ~> α2, α1 ~> α2 *) *)


End Inductives.
