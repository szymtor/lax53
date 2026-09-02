# Cross-repository handoff: Lax-53 and Lax-58

Last updated: 2026-09-02

This is the durable handoff for the coordinated work under:

```text
/Users/szymtor/Dropbox/nauka/gits/laxSubmissions
```

On resumption, read this file together with both repositories'
`FORMALIZATION_STATE.md` files and `MSO-automata-trees/AGENTS.md`. Preserve
both dirty working trees and all untracked user artifacts.

## Agreed architecture

The implemented boundary is:

```text
mathematical Lax-53 values and translations
                    |
                    v
datatype-specific constructor certificates
                    |
                    v
Lax-58 neutral structural Raw presentation
                    |
                    v
Lax-58 distinguished immutable word arena
                    |
                    v
Lax-53 specialized RAM layout and verified evaluator
```

Lax-58 contains no generic binary serialization, prefix parser, codec-based
computability interface, mutable heap, or runtime model. It supplies a small
structural vocabulary and one exact linear-footprint arena. Complete
constructor equations in the owning downstream submission are the
kernel-checked no-advice certificate.

Lax-53 keeps the mathematical formula/automaton translations at value level.
It separately certifies structural presentations of its finite automaton data,
raw formulas, and ranked trees. Its fixed-width transition table and
one-symbol-per-node postorder tree word remain a specialized RAM refinement,
not the generic representation.

No bare `Computable` statement over an arbitrary hidden coding is currently
exposed. Adding one now would choose an unrelated `Primcodable` witness and
recreate the abstraction loophole. A future effectiveness theorem should be
stated in a dedicated computation/refinement layer tied to the certified
structural representation. The existing Lean translations are concrete total
functions, and the reverse compiler is used by the RAM proof.

For the fixed-sentence theorem, sentence preprocessing is outside the measured
execution because the sentence is fixed. If the formula becomes runtime input,
the conversion cost must be included.

## Lax-58 status

Repository: `canonical-encodings`; the structural rewrite is committed as
`0994f68f21d33c6a065fd3bb4578b4bd9efb8e96`.

- Concepts: `StructuralPresentation`, `StructuralCombinators`, `WordArena`.
- Proofs for all grouped structural and arena claims compile.
- Full `lax build . --no-color` passes.
- `Presentation.Canonical` and the complete former serialization layer are
  removed.
- The arena encoder determines all stored words; density separately excludes
  unreachable blocks.
- Preserve untracked `Archive.zip` and `lax58_inmemory_patch/`.
- Do not run `lax register`.

## Lax-53 status

Repository: `MSO-automata-trees`; current HEAD before the uncommitted rewrite:
`3118d74`.

Concept changes:

- `EffectiveTranslations` uses direct `RawFormula` syntax and states two
  uniform value-level, alphabet- and language-preserving translations.
- `StructuralRepresentations` defines named presentations for ranked alphabet
  codes, transition codes, automaton bodies, encoded automata, raw formulas,
  encoded sentences, and ranked trees. Formula and tree laws cover every
  constructor; the tree uses a fixed constructor tag, explicit symbol field,
  and recursively ordered children.
- `TreeModelCheckingEncoding` is explicitly a specialized RAM layout.
- `MSOLinearTime` states the fixed-parameter preprocessing boundary and does
  not pretend formula compilation is free for a uniform runtime input.

Proof changes:

- New proofs discharge the three structural certificate groups and the pure
  value-level translation theorem.
- The formula compiler now consumes `RawFormula` directly.
- Obsolete raw-formula token parser/serializer computability modules were
  removed from the proof package.
- The revised `Lax53Proofs.MSOLinearTime` target builds successfully through
  3022 jobs, and the final `Lax53Proofs` root builds successfully through 3038
  jobs. The `Lax53` concept root builds successfully through 909 jobs.
- Source audit finds no `sorry`, `admit`, or proof-package axioms. The inactive
  legacy formula serializer/parser blocks were removed entirely.

## Local dependency and validation caveat

The Lax authors confirmed that simultaneous local development should use a
local package override pointing to the dependency submission directory. The
generated Lake manifests and package-overrides in Lax-53 point `Lax58` at the
local `canonical-encodings/concepts` directory, and direct Lake builds work.

The installed Lax CLI/spec still resolves every declared cross-submission
dependency against the Archive database before Lake is invoked. Since Lax-58
has no content-bearing Archive record, `lax build` rejects it despite the
local override. Do not publish merely to bypass this local tooling mismatch.
Record direct `lake build` results and report the Lax validation blocker
honestly.

## Preservation and next action

- Never reset or discard either dirty working tree.
- Never run `lax register`; do not submit or publish without an explicit user
  request.
- Preserve unrelated files and the two named Lax-58 artifacts.
- The implementation is ready for user review. The next technical step after
  any requested revisions is full Lax-53 validation once its local-draft
  dependency can pass Lax resolution.
