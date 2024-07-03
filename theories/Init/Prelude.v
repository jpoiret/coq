(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Coq.Init.Notations.
Require Export Coq.Init.Types.
Require Export Coq.Init.Tactics.Ltac.
Require Export Coq.Init.Tactics.Tauto.
Declare ML Module "cc_plugin:coq-core.plugins.cc".
Declare ML Module "firstorder_plugin:coq-core.plugins.firstorder".
