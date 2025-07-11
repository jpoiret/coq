#1025 Bounded Sort Polymorphism with Elimination Constraints (supplementary material)
======================================================================

This folder contains the supplementary material for submission #1025, titled "Bounded Sort Polymorphism with Elimination Constraints".
It contains a modified version of Rocq that supports algebraic universes, sort elimination constraints, and elaboration of implicit sorts and elimination constraints, as well as an initial prelude of Rocq making use of it.

The upstream Rocq repository can be found on the [Rocq Prover GitHub
repo](https://github.com/rocq-prover/rocq).


Building the supplementary material
----------------------
Usual Rocq install instructions apply to this supplementary material. These can be found in the
file `INSTALL.md`. The OPAM switch method is recommended, with a small download
footprint, and we expect a build time of maximum 10 minutes on older machines.

Using this supplementary material
-------------------

It is encouraged to use RocqIDE, built
alongside Rocq with `make Rocqide`, to browse and check the source yourself,
with the command `Rocqide`, as other interaction systems would need patches to
support this version of Rocq.

The adapted prelude of the core library is in `theories/Init`. 
See in particular `theories/Init/Specif.v` and `theories/Init/Datatypes.v` for 
adaptation of core definitions like the option type. 
The files in `theories/popl26` support the sections on large elimination
and the extracted sorts of the paper.
Other relevant examples can be found in the test suite, namely in `test-suite/success/sort_poly_elim_csts.v` and `test-suite/success/sort_poly_elab.v`.

All of these files can be checked individually by loading them in RocqIDE after having built all of Rocq with `make world`, and going
through the file using the Navigation menu, loading all relevant sentences in
the file.
