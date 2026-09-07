# Audit of the Lax-53 and Lax-58 work

## Verdict

The overall architecture is reasonable, and the audit found no obvious
semantic shortcut in the RAM work. Formula compilation is genuinely being
implemented inside a fixed program and charged to the runtime.

However, the current working trees are not submission-ready. The largest
concern is that Lax-58's advertised "no hidden advice" certification is weaker
than its documentation claims.

## Main concerns

### 1. Lax-58 does not yet formally certify naturality for derived datatypes

`structural%` is a useful and sensible tool, but its `FieldEncoding` can be any
function into `Raw`. Such a function could attach computed advice while
remaining injective.

Lax-53 currently proves only that the resulting tree and sentence
presentations round-trip. Lawfulness or injectivity alone does not exclude an
extra satisfiability bit or another derived annotation.

The current encodings themselves look natural, but the reusable contract is
weaker than the claim. Recommended alternatives are:

- restore explicit datatype-specific constructor-law structures; or
- have Lax-58's derivation tool generate a first-class certificate containing
  all constructor equations.

The macro should remove boilerplate rather than replace the kernel-checked
structurality certificate.

Relevant locations:

- `../canonical-encodings/concepts/Lax58/StructuralDerivation.lean`, especially
  `FieldEncoding`;
- `concepts/Lax53/StructuralRepresentations.lean`, especially `tree_lawful`
  and `sentence_lawful`.

### 2. There are definite Lax validation blockers

- `proofs/Lax53Proofs/RuntimeLayout.lean` declares names under
  `Lax53.TreeModelCheckingEncoding`, although proof-package declarations must
  live under `Lax53Proofs`.
- The proof root does not directly import `Lax53Proofs.RuntimeLayout`; Lax
  requires exact direct root imports.
- `proofs/RadixScratch.lean` is scratch material inside the proof package but
  outside `Lax53Proofs/`; it must be removed or relocated before validation.
- The proof package directly requires `Lax58Proofs`, but not the `Lax58`
  concept package, while proofs directly use Lax-58 axioms such as
  `constructor_eq_iff`, `sizeLaws`, and `encodeRaw_represents`. Under the
  current specification, transitive reachability is insufficient. Prefer
  using the assumption-free theorems from `Lax58Proofs`, or add a direct
  concept dependency.

Relevant locations:

- `proofs/Lax53Proofs/RuntimeLayout.lean`;
- `proofs/Lax53Proofs.lean`;
- `proofs/RadixScratch.lean`;
- `proofs/lakefile.toml`;
- `proofs/Lax53Proofs/MSORamArenaRead.lean`;
- `proofs/Lax53Proofs/AutomatonRamArenaBounds.lean`;
- `proofs/Lax53Proofs/StructuralRepresentations.lean`;
- `proofs/Lax53Proofs/MSOLinearTime.lean`.

### 3. Lax-53 still has three unproved public statements

At the audited snapshot, ten of thirteen concept axioms had annotated proofs.
The missing statements were:

- `Lax53.TreeModelCheckingEncoding.automatonInput_length`, apparently a small
  oversight;
- `Lax53.MSOLinearTime.exists_uniform_msoModelChecking`;
- `Lax53.MSOLinearTime.exists_fixed_sentence_modelChecking`.

The low-level compiler work is substantial and internally coherent, but the
headline theorem is still genuinely incomplete.

### 4. Cross-repository state is inconsistent

Lax-53 pins Lax-58 at commit `0994f68f21d33c6a065fd3bb4578b4bd9efb8e96`,
which does not contain the new untracked `StructuralDerivation` module. Final
validation therefore requires reviewing, committing, and submitting the new
Lax-58 revision, then updating Lax-53's pin.

Lax-58's handoff still says "exactly three concepts" and "proof adaptation
pending", while its current root has four concepts and its current
`build-output.json` records all fifteen Lax-58 proof conclusions successfully.
The abstracts also do not accurately describe the new derivation tool or
Lax-53's stronger uniform theorem.

Additionally, Lax-58 now contains proved helper theorems inside concept files,
contrary to the requested concept/proof separation.

## What looks good

- Intrinsic Lax-52 formulas remain the sole public formula syntax.
- Value-level MSO/automaton translations are cleanly separated from machine
  representation.
- The distinguished Lax-58 arena is explicit, dense, and exact-sized.
- The automaton-acceptance RAM theorem appears fully implemented.
- The new IMP+ fragments are fixed commands; runtime values arrive through
  the arena and registers.
- No `sorry`, `admit`, or proof-package axioms were found.

## Recommended order of work

1. Review and freeze the four-module Lax-58 concept surface, especially the
   first-class structurality-certificate story.
2. Reconcile Lax-58's abstract, proposal, handoff, proof placement, and current
   validated output.
3. Commit and submit the reviewed Lax-58 draft, then update the Lax-53 pin.
4. Repair the Lax-53 namespace, root-import, scratch-file, and axiom-hygiene
   blockers.
5. Add the small missing `automatonInput_length` proof.
6. Complete the charged MSO compiler, compose it with the automaton backend,
   and prove both MSO runtime statements.
7. Run a complete Lax build and kernel replay once dependency resolution is
   reproducible.

The size of the proof development--about 30,300 lines across more than one
hundred proof modules at the audited snapshot--is not by itself suspicious for
a direct charged word-RAM verification. Still, expanding it further before
settling the Lax-58 interface would increase rework risk.

This audit was performed read-only while another agent was actively modifying
the repository. Individual transient packaging issues may already be under
repair.
