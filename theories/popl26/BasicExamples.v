
(* Examples shown in Section 2.2 of the paper *)

(* If viewing this file in RocqIDE, consider enabling the `Display universe levels`.
   This will allow printing and viewing the actual elimination constraints elaborated in the different terms.
   To do this:
   1. Open the `View` menu at the top of the editor, and
   2. Check the checkbox titled `Display universe levels`.
*)

Set Universe Polymorphism.


(************************************************)
(*              Dependent Pairs                 *)
(************************************************)
Section DependentPairs.

  Inductive sigma (A:𝒰) (B:A -> 𝒰) : 𝒰 :=
    pair : forall x : A, B x -> sigma A B.

  Print sigma.
  Print sigma_poly.

  (* Universe levels are omitted in the paper but are necessary *)
  Definition ex@{i j}   := sigma@{Type Prop Prop; i j}.
  Definition exist@{i j} := pair@{Type Prop Type; i j}.
  Print ex.

  Arguments pair {A}.

  Definition sig@{i j}  := sigma@{Type Prop Type; i j}.
  Print sig.

  Definition sigT@{i j} := sigma@{Type Type Type; i j}.
  Print sigT.

  Definition sig_rect@{i j k} := sigma_poly@{Type Type Type Type; i j k}.
  Definition sig_ind@{i j k} := sigma_poly@{Type Type Type Prop; i j k}.
  Definition sig_sind@{i j k} := sigma_poly@{Type Type Type SProp; i j k}.

  Section Subset_projections.
    Variable A : 𝒰.
    Variables B : A -> 𝒰.

    Definition proj1_sigma (e:sigma A B) := match e with
                                      | pair _ a b => a
                                      end.

    Print proj1_sigma.

    Definition proj2_sigma (e:sigma A B) :=
      match e return B (proj1_sigma e) with
      | pair _ a b => b
      end.

     Print proj2_sigma.

  End Subset_projections.
End DependentPairs.

(************************************************)
(*                    Records                   *)
(************************************************)

Section Records.
  Set Primitive Projections.
  Record Prod (A: 𝒰) (P: A -> 𝒰): 𝒰 := { fst: A ; snd: P fst }.

  Print Prod.

  Definition ProdTP@{s; u1 u2} := Prod@{Type Prop s; u1 u2}.
End Records.

(************************************************)
(*                    Lists                     *)
(************************************************)

Section Lists.
  Inductive list (A : 𝒰) : 𝒰 :=
   | nil : list A
   | cons : A -> list A -> list A.

  Arguments nil {A}.
  Arguments cons {A} a l.

  Print list.

  Fixpoint map {A B : 𝒰} (f : A -> B) (l : list A) : list B :=
    match l with
      | cons a l => cons (f a) (map f l)
      | nil => nil
    end.

   Print map.

   Section Bool.

    Inductive bool : 𝒰 := true | false.

    Print bool.

    Definition andb (b1 b2 : bool) : bool := if b1 then b2 else false.

    Print andb.

    Fixpoint allb {A : 𝒰} (p : A -> bool) (l : list A) : bool :=
      match l with
      | nil => true
      | cons hd tl => andb (p hd) (allb p tl)
      end.

    Print allb.

  End Bool.
End Lists.
