#!/bin/bash

# Check if OPAM is installed
if ! command -v opam &>/dev/null; then
  echo "Error: OPAM is not installed."
  echo "Please install OPAM using your package manager, e.g.,"
  echo "'sudo apt install opam' or 'brew install opam'"
  exit 1
fi

# Check if OPAM is initialized
if [ ! -d "$HOME/.opam" ]; then
  echo "OPAM is not initialized. Running 'opam init'..."
  opam init --yes || {
    echo "Failed to initialize OPAM"
    exit 1
  }
  echo "OPAM initialized."
fi

echo "OPAM is ready. Version: $(opam --version)"

# Define the switch name
SWITCH_NAME="popl26-paper-1025-elim-constraints-artifact"
OCAML_VERSION="4.14.0"

echo "Starting OPAM environment setup..."
echo "Target switch: '$SWITCH_NAME'"
echo "OCaml version: '$OCAML_VERSION'"

# Check if the switch exists
if opam switch list --short | grep -q "^${SWITCH_NAME}$"; then
  echo "The switch '$SWITCH_NAME' already exists."

  # Prompt user to remove it
  read -p "Do you want to remove it and recreate it? [Y/n]: " REPLY
  REPLY=${REPLY:-Y}

  if [[ "$REPLY" =~ ^[Yy]$ ]]; then
    echo "Removing switch '$SWITCH_NAME'..."
    opam switch remove "$SWITCH_NAME" -y
    echo "Switch removed."
    # Create the switch
    echo "Creating switch '$SWITCH_NAME' with OCaml version '$OCAML_VERSION'..."
    opam switch create "$SWITCH_NAME" "$OCAML_VERSION"
  else
    echo "Keeping existing switch."
  fi
fi

# Set the environment for the new switch
echo "Activating switch '$SWITCH_NAME'..."
eval $(opam env)

# Install Rocq dependencies
echo "Installing Rocq dependencies..."
opam install --deps-only . -y

echo "OPAM environment setup complete."

# Prompt user to build project
read -p "Do you want to build and install the project now? [Y/n]: " REPLY
REPLY=${REPLY:-Y}

if [[ "$REPLY" =~ ^[Yy]$ ]]; then
  echo "Cleaning any previous builds."
  make clean
  echo "Building the project."
  make world
  echo "Project built."
  echo "Building RocqIDE."
  make rocqide
  echo "RocqIDE built."
  echo "Installing project in switch."
  dune install rocq-runtime coq-core rocq-core coqide-server rocqide
  echo "Installation completed. You can now explore the relevant files in the artifact."
else
  echo "Not building the project. It needs to be built manually to evaluate the artifact. Exiting."
  exit 0
fi
