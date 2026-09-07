#!/usr/bin/env bash
set -euo pipefail

report_proofs=false
case "${1:-}" in
  "") ;;
  --proofs) report_proofs=true ;;
  *) echo "Usage: bash scripts/certificate-report.sh [--proofs]" >&2; exit 2 ;;
esac
if (( $# > 1 )); then
  echo "Usage: bash scripts/certificate-report.sh [--proofs]" >&2
  exit 2
fi

script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
cd -- "$script_dir/../concepts"
# Keep build chatter off stdout so reports can be compared directly.
lake build Lax53.StructuralRepresentations >&2
lake env lean "-Dpp.proofs=$report_proofs" ../tests/CertificateReport.lean
