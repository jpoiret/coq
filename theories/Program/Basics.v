(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(** Standard functions and combinators.

   Proofs about them require functional extensionality and can be found
   in [Combinators].

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** The polymorphic identity function is defined in [Datatypes]. *)

#[global]
Hint Unfold compose : core.

Declare Scope program_scope.

Notation " g ∘ f " := (compose g f)
  (at level 40, left associativity) : program_scope.

Local Open Scope program_scope.
