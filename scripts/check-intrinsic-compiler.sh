#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd -- "$script_dir/../proofs"
lake build Lax53Proofs.IntrinsicUniformModelChecking Lax53Proofs.FixedSentenceModelChecking
lake env lean ../tests/ArrayInput.lean
lake env lean ../tests/IntrinsicCompilerBridge.lean
lake env lean ../tests/IntrinsicPublicCompiler.lean
lake env lean ../tests/IntrinsicParameterBounds.lean
lake env lean ../tests/FixedSentenceModelChecking.lean
lake env lean ../tests/RamComplexityStatements.lean
