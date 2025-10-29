#!/bin/bash

# Colors
GREEN="$(tput setaf 2)"
RED="$(tput setaf 1)"
YELLOW="$(tput setaf 3)"
BLUE="$(tput setaf 4)"
SKY_BLUE="$(tput setaf 6)"
RESET="$(tput sgr0)"

# Functions for formatted messages
ok() { echo "${GREEN}[OK]${RESET} $1"; }
error() { echo "${RED}[ERROR]${RESET} $1"; }
warn() { echo "${YELLOW}[WARN]${RESET} $1"; }
info() { echo "${BLUE}[INFO]${RESET} $1"; }
action() { echo "${SKY_BLUE}[ACTION]${RESET} $1"; }

# Check if OPAM is installed
if ! command -v opam &>/dev/null; then
  error "OPAM is not installed."
  info "Please install OPAM using your package manager, e.g.,"
  info "'sudo apt install opam' or 'brew install opam'"
  exit 1
fi

# Check if OPAM is initialized
if [ ! -d "$HOME/.opam" ]; then
  warn "OPAM is not initialized. Running 'opam init'..."
  if ! opam init --yes; then
    error "Failed to initialize OPAM"
    exit 1
  fi
  ok "OPAM initialized."
fi

ok "OPAM is ready. Version: $(opam --version)"

# Define the switch name
SWITCH_NAME="popl26-paper-1025-elim-constraints-artifact"
OCAML_VERSION="4.14.0"
action "Starting OPAM environment setup..."
info "Target switch: '$SWITCH_NAME'"
info "OCaml version: '$OCAML_VERSION'"

# Create the switch
create_switch() {
  action "Creating switch '$SWITCH_NAME' with OCaml version '$OCAML_VERSION'..."
  if ! opam switch create "$SWITCH_NAME" "$OCAML_VERSION"; then
    error "Failed to create switch '$SWITCH_NAME'"
    exit 1
  fi
  ok "Switch created."
}

# Check if the switch exists
if opam switch list --short | grep -q "^${SWITCH_NAME}$"; then
  warn "The switch '$SWITCH_NAME' already exists."
  # Prompt user to remove it
  read -p "Do you want to remove it and recreate it? [Y/n]: " REPLY
  REPLY=${REPLY:-Y}
  if [[ "$REPLY" =~ ^[Yy]$ ]]; then
    action "Removing switch '$SWITCH_NAME'..."
    if ! opam switch remove "$SWITCH_NAME" -y; then
      error "Failed to remove switch '$SWITCH_NAME'"
      exit 1
    fi
    ok "Switch removed."
    # Recreate the switch
    create_switch
  else
    info "Keeping existing switch."
  fi
else
  # Create the switch
  create_switch
fi

# Set the environment for the new switch
action "Activating switch '$SWITCH_NAME'..."
eval $(opam env)

# Install Rocq dependencies
action "Installing Rocq dependencies..."
if ! opam install --deps-only . -y; then
  error "Failed to install dependencies"
  exit 1
fi
ok "OPAM environment setup complete."

# Prompt user to build project
read -p "Do you want to build and install the project now? [Y/n]: " REPLY
REPLY=${REPLY:-Y}
if [[ "$REPLY" =~ ^[Yy]$ ]]; then
  action "Cleaning any previous builds."
  if ! make clean; then
    warn "Failed to clean previous builds"
  fi
  action "Building the project."
  if ! make world; then
    error "Failed to build the project"
    exit 1
  fi
  ok "Project built."
  action "Building RocqIDE."
  if ! make rocqide; then
    error "Failed to build RocqIDE"
    exit 1
  fi
  ok "RocqIDE built."
  action "Installing project in switch."
  if ! dune install rocq-runtime coq-core rocq-core coqide-server rocqide; then
    error "Failed to install project"
    exit 1
  fi
  ok "Installation completed. You can now explore the relevant files in the artifact."
else
  info "Not building the project. It needs to be built manually to evaluate the artifact. Exiting."
  exit 0
fi
