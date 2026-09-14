#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd -- "$script_dir/../proofs"
lake build Lax842588Proofs.PrimitiveRecursiveAutomata
lake env lean ../tests/PrimitiveRecursiveBridge.lean
