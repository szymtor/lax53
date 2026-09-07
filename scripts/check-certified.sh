#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd -- "$script_dir/../concepts"
lake build Lax53.StructuralRepresentations
lake env lean ../tests/CertifiedRepresentations.lean
cd -- ../proofs
lake build Lax53Proofs.StructuralRepresentations
