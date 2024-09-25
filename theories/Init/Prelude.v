(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Stdlib.Init.PreludeOptions.
Require Export Stdlib.Init.Notations.
Require Export Stdlib.Init.Types.
Require Export Stdlib.Init.Tactics.Ltac.
Require Export Stdlib.Init.Tactics.Tauto.
Require Export Stdlib.Init.Tactics.Extra.
Declare ML Module "cc_core_plugin:coq-core.plugins.cc_core".
Declare ML Module "cc_plugin:coq-core.plugins.cc".
Declare ML Module "firstorder_core_plugin:coq-core.plugins.firstorder_core".
Declare ML Module "firstorder_plugin:coq-core.plugins.firstorder".
