# Bounded Sort Polymorphism with Elimination Constraints (Artifact)

This folder contains the artifact for the paper titled "Bounded Sort Polymorphism with Elimination Constraints".
It contains a modified version of Rocq that supports algebraic universes, sort elimination constraints, and elaboration of implicit sorts and elimination constraints, as well as an initial prelude of Rocq making use of it.

The upstream Rocq repository can be found on the [Rocq Prover GitHub repo](https://github.com/rocq-prover/rocq).

## Hardware dependencies

No specific hardware dependencies.

## Getting Started

All of the code has been developed and built with Ocaml v4.14.0.

We provide a script for a local setup, using `opam`, that installs and builds everything. The specific instructions can be found in the [corresponding section](#local-setup-with-opam).

Otherwise, usual Rocq installation instructions apply to this artifact. These can be found in the
file `INSTALL.md`. The OPAM switch method is recommended, with a small download
footprint, and we expect a build time of maximum 10 minutes on older machines.

To navigate the code, claims of the paper, and interactively check the proofs and definitions,
we encourage the reader to use RocqIDE, built
alongside Rocq with the provided `opam` script (or by executing `make Rocqide` manually), as other IDEs would need patches to
support this version of Rocq.
To run RocqIDE, it suffices to call the command `Rocqide`, which will open the application.

Alternatively, we recommend the reader to use [VS Code](https://code.visualstudio.com/download) with the [VsCoq Legacy plugin](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1).
This alternative requires updating the `coqtop` path setting, which should be set to `_build/install/default/bin/`.

### Local Setup (with Opam)

We include a shell script `opam-artifact-setup.sh` that creates a new opam switch named `popl26-paper-1025-elim-constraints-artifact` and installs all the necessary requirements. The script also prompts whether to build the project immediately or to wait, letting one build it manually. The specific steps are the following:

1. Run `./opam-artifact-setup.sh`.
1. Accept or reject the prompt asking whether to build the project immediately.
1. Accept or reject the prompt asking whether to build and install `RocqIDE` in the switch.

## Step-by-step instructions and list of claims

Following the steps from the previous section already builds every proof and definition in the project.
Therefore, in this section we focus on providing specific details on some paper-to-artifact correspondences and files to look at.
All of these files can be checked individually by loading them in RocqIDE after having built all of Rocq with `make world`, and going
through the file using the Navigation menu, loading all relevant sentences in the file.

First, the adapted prelude of the core library can be found in the folder `theories/Init`.
See in particular `theories/Init/Specif.v` and `theories/Init/Datatypes.v` for
adaptation of core definitions like the `option` type.

The files in `theories/popl26` support the sections on large elimination (Section XXX)
and the extracted sorts of the paper (Section XXX).

Finally, other relevant examples can be found in the test suite, namely in `test-suite/success/sort_poly_elim_csts.v` and `test-suite/success/sort_poly_elab.v`.


## Reusability

## License

This project is distributed under the terms of the XXX license.
