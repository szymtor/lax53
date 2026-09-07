# Lax-53 current state

Updated: 2026-09-07. Validated source on `main`; publication is the next step.
The public RAM statements now use Lax-58's reusable
`RamComputableWithinUsing` predicate. Their encodings, algorithms, bounds, and
quantifier order are unchanged: the concise proofs unfold the predicate and
invoke the previously proved expanded implementation theorems. The two
automata/MSO directions share `MSOTreeAutomataEquivalence.lean` with the
equivalence statement.

## Implemented versus unfinished

- Structural encoding boilerplate is replaced by four certified derivations
  in `concepts/Lax53/StructuralRepresentations.lean`: terms, relations,
  intrinsic Lax-52 formulas, and ranked trees. The closed Lax-58 resolver
  ignores arbitrary `FieldEncoding` instances and transitively bottoms out
  in Nat/Fin. Encoders, complete laws, and certificates remain inspectable.
- **The complete public-input RAM implementation now builds.**
  `IntrinsicModelCheckingRam.exists_ram` chooses one compiler code and one
  finite layout before any alphabet, sentence, tree, or word width. It reads
  the unchanged certified input, compiles the whole intrinsic sentence during
  the measured run, materializes the exact automaton table and tree word,
  evaluates the tree, and emits its sentence-satisfaction bit.
- This result starts from the actual zero-memory RAM convention. Logical
  workspace extents are not stored in machine memory; no numeric formula,
  compiled automaton, nonzero workspace, or other advice is supplied.
- **Both concise headline runtime theorems now build.**
  `IntrinsicUniformModelChecking.exists_uniform_msoModelChecking_proof`
  discharges the explicit compiler, arena, workspace, and layout premises
  with primitive-recursive parameter-only coefficients. Its tree dependence
  is linear and its public input and word-bound convention are unchanged.
  `FixedSentenceModelChecking.exists_fixed_sentence_modelChecking_proof`
  receives only the tree. Its program contains a fixed automaton, materializes
  it during the counted run, and starts with zero memory, not a supplied table.
- The accepted simplification is implemented: reuse one verified
  primitive-recursive-to-RAM bridge for the complete pure compiler.
  The previous bespoke sparse-valid/automaton-operation route is preserved
  but is not the active route.

## Proof-side interfaces to reuse

- The seven-case generic bridge is complete through primitive recursion,
  bounded execution, finite layouts, and actual RAM realization. Its
  intersection example and the complete normalized-field compiler are proved.
- `IntrinsicCompilerFields` derives six-word rows from original formula
  occurrences; a stack fold agrees with `IntrinsicFormulaCompiler.compileFormula`.
  Every unused field is zero. Rows contain neither tree data nor arena addresses.
- `IntrinsicCompilerFromArena` composes counted alphabet/formula packing,
  primitive-recursive compilation, and flat table unpacking. Only `P` is written;
  there is no tape I/O. The typed compiler's outer `some` tag is removed
  during the measured materialization.
- `IntrinsicCompilerPrepare` establishes that body's precondition using the
  public arena reader, opener, alphabet reader, and complete formula traversal.
  `IntrinsicCompilerFrame` proves preservation of the arena and tree pointer.
  `IntrinsicPublicCompiler` connects public input to the exact compiled table
  while retaining the represented tree for the next phase.
- `IntrinsicEvaluatorHeader` initializes table scalars without another
  `read "n"`. `IntrinsicEvaluatorPrepare` reads the retained tree and establishes
  the existing `EvaluateTreeContext`.
- `IntrinsicSentenceCorrectness` proves the zero-scope symbol numbering agrees
  with the original alphabet, so the compiled table decides the original
  sentence language without an additional runtime relabeling operation.
- `IntrinsicModelChecking` composes compilation, tree preparation, and
  `automatonBackend_spec`; `initial_initEnv` establishes its precondition
  from zero arrays and the public input. `IntrinsicModelCheckingRam` transfers
  that complete counted run to actual Lax-13 instructions.
- `ImpLayout.exists_layout` proves every finite IMP command admits a finite,
  input-independent layout. Use it for the assembled program instead of
  maintaining another global register inventory.
- `IntrinsicParameterFields` supplies the field-level parameter bounds:
  occurrence scopes are at most initial scope plus three times formula
  structural size; sentence field values are at most
  `8 + alphabet.length + maximumRank alphabet + 3 * sentenceSize alphabet φ`.
- `CompilerNumericBounds` and `IntrinsicParameterEncoding` bound numeric
  alphabet/formula encoding using bounded lists and finite-prefix maxima.
  `IntrinsicCompilerParameters` discharges all compiler-specific word premises;
  `IntrinsicCompiledTableBounds` bounds table values and dimensions.
  `IntrinsicInputBounds`, `IntrinsicTimeBounds`, and `IntrinsicWordBounds`
  assemble the public linear time/word coefficients, including layout addresses.
- `FixedTableLoader`, `FixedSentencePrepare`, and `FixedAutomatonModelChecking`
  reuse the checked decoder, arena reader, tree preparation, and evaluator
  for the fixed-sentence companion. The uniform compiler is unchanged; only
  the companion is allowed to specialize before program choice.

## Validation and trust boundary

- Full local proof-root build passes:
  `env LEAN_NUM_THREADS=2 lake build Lax53Proofs` (3156 jobs, session `12059`).
  This includes all twelve new bound/headline/fixed-sentence modules.
  The public RAM target independently passes (3113 jobs).
- Direct axiom audits of the new public frontend, complete IMP model checker,
  actual RAM theorem, initialization, layout existence, and sentence semantics
  report only `propext`, `Classical.choice`, and `Quot.sound`.
  Two inherited concept-axiom references were replaced by proved counterparts:
  arena representation in `MSORamArenaRead`, and constructor injectivity in
  `FormulaArenaTraversalBody`.
- Focused regressions pass: `bash scripts/check-intrinsic-compiler.sh`
  (3129 build jobs, four test files, session `23121`). Both headline proof
  types match the unchanged concept statements; all 38 axiom guards report
  only the three permitted background axioms.
- Explicit kernel replay of all twelve latest modules passes in session
  `24524`, with `LEAN_NUM_THREADS=2`. Earlier public-input and bridge replay
  milestones remain passed as well. All checks are terminal; none is running.
- Root-module inventory and whitespace checks pass. The twelve latest modules
  contain no `sorry`, `admit`, or axiom declaration.
- Earlier unchanged checks remain passed: closed certification regressions,
  all four generated witness axiom audits, both certificate-report modes,
  Lax-58 full validation/replay, and generic bridge regressions/replay.
  The generator establishes datatype provenance; the kernel checks expanded
  output. Private constructors alone are not an unforgeability claim.
- Both certification suites were rerun successfully after the headline proofs:
  `bash canonical-encodings/scripts/check-certified.sh` followed by
  `bash MSO-automata-trees/scripts/check-certified.sh` (session `7534`).

## Current validation and preview

- Full proof-root build after the final statement-only simplification passed:
  3154 jobs. A focused 3130-job build of all four concise wrapper proofs and
  the six-file compiler regression suite also passed, including exact
  statement/proof type checks and raw-encoding identity checks.
- Standard `lax build . --no-color` passed after syncing the Archive index:
  1m26s.
  It inspected 10 concepts and 15 annotated proofs. Both MSO runtime headlines
  and all three statements in the consolidated equivalence concept have empty
  non-background assumption sets in the generated report.
- Preview regenerated September 7 and opened at
  http://localhost:8126/lax-53/. Verified the combined equivalence concept and
  all four concise runtime claims are shown as proven; the old expanded
  premise lists are no longer the public statements.
- Reader syntax/cost/frame/axiom regression passed (`71748`); all three
  merged-statement proof types passed (`40973`). The fresh six-file regression
  run `71294` also passed: reader, merged concept, internal compiler bridge,
  public compiler, parameter bounds, and fixed-sentence theorem.
- User-requested wording edits prefer "tree automata" in the
  abstract, submission title, concept titles, and explanatory comments.
  Finite-state assumptions and finite input trees remain explicit. All six
  edited Lean files have identical non-comment content.
- Final independent `lax build . --replay --no-color` passed: kernel replay
  42m12s, statement inspection 19s, total 42m38s. The seven reported warnings
  concern discouraged proof dependencies, draft dependencies, and Lax13's
  successor; none is a build or proof failure.

## Publication

The user requested commit and submission. Validation and preview are complete.
Publish the current source at `https://github.com/szymtor/lax53`, bind it to
the existing control issue 53 through the CLI, and submit it as a draft.
Issue 53 was initialized on August 10 but has no submit command/source snapshot;
the Archive record is still `init` and the live page is absent. Monitor the
exact submit handle through the Archive's independent build/replay and
publication result. Do not register.

The dependency mismatch is resolved: Lax58 and Lax58Proofs pin the published
`szymtor/lax58@83d795f06ae20b48ceed34a9f1284975d305b9c4`; Lax62Proofs is no
longer required. `Lax53Proofs.ArrayInput` contains only the old Lax13 reader
and supporting proofs, with upstream attribution. The concepts and public RAM
model did not change for this localization. The subsequent concept consolidation
was separately requested by the user.

Warnings from standard validation are informational: two proof-package
dependencies, three draft-package requirements, and Lax13 having a successor
(Lax67). They did not fail the build. Previous interrupted attempts and the
exact provenance of the localized reader are recorded in `SESSION_HISTORY.md`.

Two package `.DS_Store` files remain recoverably moved to
`/private/tmp/lax53-layout.gqgzSe/`. Preserve the extensive dirty worktree.

Workflow: [WORKFLOW.md](WORKFLOW.md). History: [SESSION_HISTORY.md](SESSION_HISTORY.md).
