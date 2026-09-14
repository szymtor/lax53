# Lax-53 / Lax-58 boundary

Updated: 2026-09-06. Read the two current-state documents first:

- [Lax-53](CURRENT_STATE.md): charged intrinsic-formula compiler and RAM evaluator.
- [Lax-58](../canonical-encodings/CURRENT_STATE.md): structural provenance and immutable arena.

## Ownership

Intrinsic mathematical values → closed constructor derivation → neutral
`Raw` structure → distinguished immutable word arena → charged Lax-53
runtime refinement and evaluation.

Lax-58 owns the structural vocabulary, fail-closed derivation, and exact arena
contents/footprint. Its low-level `FieldEncoding` is not a certificate.
The generator establishes constructor provenance and the kernel checks the
expanded laws; private constructor visibility alone provides no guarantee.
`CertifiedDerivation` contains only agreement definitions;
`CertifiedDerivationElab` contains the closed tooling. Both are explicitly
labeled infrastructure under Lax's current all-modules-are-concepts rule.

Lax-53 owns its four datatype derivation invocations, presentations, value-level
translations, and all specialized mutable storage and machine programs.
Compiling a runtime input formula must happen in the measured RAM execution.
The pure compiler is a semantic specification, not free runtime preprocessing.
Its public complexity theorems use Lax-58's `RamComputableWithinUsing` wrapper;
their proof modules retain the expanded width/resource premises and discharge
the wrapper by definitional reduction.

## Cross-repository changes

For a shared encoding/API change, run Lax-58's regression suite and replay,
Lax-53's focused suite and expanded certificate report, then its full proof
root. Preserve raw layout unless a representation change is explicitly intended.
The procedures and compiler checklist are in each repository's `WORKFLOW.md`.

Local Lake overrides support simultaneous development. They do not bypass
the installed Lax CLI's archive-record checks. Current archive blockers and
exact Lax62Proofs pins are recorded only in Lax-53's current state to avoid
duplicated, drifting status. Never publish or register merely to unblock a
local build; registration belongs to the user.

Both working trees already contain substantial user work. Preserve unrelated
changes and Lax-58's `Archive.zip`. Historical decisions remain in each
repository's `SESSION_HISTORY.md`; `FORMALIZATION_STATE.md` is a compatibility
pointer, not another independently maintained status document.
