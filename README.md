# Bounded Sort Polymorphism with Elimination Constraints (Artifact)

This folder contains the artifact for the paper titled "Bounded Sort Polymorphism with Elimination Constraints".
It contains a modified version of Rocq that supports algebraic universes, sort elimination constraints, and elaboration of implicit sorts and elimination constraints, as well as an initial prelude of Rocq making use of it.

The upstream Rocq repository can be found on the [Rocq Prover GitHub repo](https://github.com/rocq-prover/rocq).

## Hardware dependencies

No specific hardware dependencies.

## Getting Started

All of the code has been developed and built with Ocaml v4.14.0.

#### Setting up

We provide a script for a local setup, using `opam`, that installs and builds everything.
We recommend using this approach to setup the project.
The specific instructions can be found in the [corresponding section](#opam-setup).
After setting up, consider reading the [how to navigate the code section](#navigating-the-code).

Alternatively, Rocq already provides a Nix setup with the necessary dependencies. Check the [corresponding section](#nix-setup) below for more details.

Otherwise, usual Rocq installation instructions apply to this artifact. These can be found in the
file `INSTALL.md`. The OPAM switch method is recommended, with a small download
footprint, for which we expect a build time of maximum 10 minutes on older machines.

#### Navigating the code

To navigate the code, claims of the paper, and interactively check the proofs and definitions,
we encourage the reader to use RocqIDE, built
alongside Rocq with the provided `opam` script (or by executing `make Rocqide` manually), as other IDEs may need patches or specific configurations to
support this version of Rocq.
To run RocqIDE, it suffices to call the command `rocqide`, which will open the application.
For example, running `rocqide test-suite/success/sort_poly_elab.v` will open the corresponding file with the IDE.

Alternatively, we recommend the reader to use [VS Code](https://code.visualstudio.com/download) with the [VsCoq Legacy plugin](https://marketplace.visualstudio.com/items?itemName=coq-community.vscoq1).
If the project is built following the [opam instructions](#opam-setup), then the binaries are installed in the opam switch and available in the environment, therefore the VsCoq plugin should work out of the box.
If the binaries cannot be found, then one can set the path to them manually:
1. Go to Settings > Extensions > Coq configuration
1. Look for the `Coqtop: Bin Path` configuration variable (otherwise, use the `Search settings` input field at the top of the settings and search for `coqtop`)
1. Enter the value `_build/install/default/bin` in the input field.
1. (optional) Restart the extensions or VSCode to make sure the changes are applied.

### Opam setup

We include a bash script `opam-artifact-setup.sh` that:
1. Creates a new opam switch named `popl26-paper-1025-elim-constraints-artifact`,
1. installs all the necessary dependencies, and
1. builds Rocq and RocqIDE, and installs them in the switch.

The specific steps to setup the project are the following:

1. Run `./opam-artifact-setup.sh`.
1. Accept or reject the prompt asking whether to build and install the project immediately. This builds Rocq and RocqIDE.

It is now possible to browse the source code and Rocq files.
Check the [Navigating the code](#navigating-the-code) section for details on running the RocqIDE or VSCode to explore the project and claims of the paper.

### Nix setup

Rocq provides a `flake.nix` file with all the necessary dependencies.
In order to build the project, it suffices to launch a `nix-shell` and manually execute `make world` and `make rocqide`.
Note that the binaries one should use to navigate the code are not installed in the (non-existing) opam switch, hence when you follow the instructions in [navigating the code](#navigating-the-code), one should use the binaries built in `_build/install/default/bin`.

## Step-by-step instructions and list of claims

Following the steps from the previous section already builds every proof and definition in the project.
Therefore, in this section we focus on providing specific details on some paper-to-artifact correspondences and files to look at.
All of these files can be checked individually by loading them in RocqIDE, and going
through the files using the Navigation menu, which loads all relevant sentences in the file.

First, the adapted prelude of the core library can be found in the folder `theories/Init`.
See in particular `theories/Init/Specif.v` and `theories/Init/Datatypes.v` for
adaptation of core definitions like the `option` type.

The files in `theories/popl26` support the examples in Section 2:
- `BasicExamples.v` contains examples from Section 2.2.
- `ExtractionSort.v` contains the example from Section 2.3, plus the `nat_discr_(info|erase)` lemmas from Section 2.4.
- `LargeElim.v` contains an example of large elimination, mentioned in Section 2.4.
- `Impredicativity.v` contains the example on inheritance of impredicativity, illustrated in Section 2.4.

Finally, other relevant examples can be found in the test suite, namely in `test-suite/success/sort_poly_elim_csts.v` and `test-suite/success/sort_poly_elab.v`.

## Reusability

## License

This project is distributed under the terms of the GNU Lesser General Public License Version 2.1.
