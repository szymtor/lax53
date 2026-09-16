# Finalization authorized — in progress (2026-09-16)

The user explicitly requested submission, consistent GPT author credits, and
final registration of the current submissions. This supersedes the earlier
keep-draft restriction and repository instructions against registration for
this release. Preserve the model/version suffixes in the author names.

Publish and register in dependency order, updating downstream pins to each
accepted final source commit. Register only after verifying the Archive has
accepted that exact commit and the intended metadata and proof obligations.
The local tree preview was reviewed before this authorization.

Next: complete validation, publish the updated draft, verify it, and register.
The records below describe earlier checkpoints; none implies this release is
already published or registered.

## Previous status

# Nine-claim interface: validated locally; preview ready for review

Updated 2026-09-16. User authorized implementing the agreed interface cleanup,
with a local preview for review **before submission**. Do not submit or register.

- Six public axioms/annotations are removed; their ordinary proof lemmas remain:
  formula/tree structurality, the two input-length facts, fixed-automaton
  acceptance, and fixed-sentence model checking. Nine public claims remain.
- Abstract complementation uses the public determinization contract; equivalence
  uses the two public directional contracts. The fixed-automaton helper now
  specializes uniform acceptance. The tree-only fixed-sentence proof is retained.
- Concept root build passed (960 jobs), using the explicit local dependency
  overrides in `../migration-tools/ram-808846-local-overrides.json`.
- Full proof root build passed (3222 jobs). The fixed-automaton specialization
  required unfolding `WordArena.encode` to identify the two input tapes.
  Final log: `../migration-tools/trees-interface-proof-build-final.log`.
- Five focused regressions passed: certified representations, logical
  equivalence/dependencies, intrinsic parameter bounds, tree-only fixed-sentence
  model checking, and the uniform/fixed-automaton statement types and axioms.
  Results: `../migration-tools/trees-interface-regressions.json`.
- The type/axiom audit passed for all nine retained public claims and four
  canonical discharge proofs. Four local annotated proofs have empty
  non-background assumption sets; five use exactly the expected public
  contracts. The dependency graph is closed. Log:
  `../migration-tools/trees-interface-audit.log`.
- Fresh official Lax static validation and inspection judging passed with
  zero violations: ten concept modules, nine statements, nine annotated proofs.
  Inspection reports 362 unused-helper warnings; those implementation helpers
  are intentionally retained. Static checks retain the two proof-package
  dependency warnings. Log: `../migration-tools/trees-interface-inspection.log`.
- Normal Archive resolution remains blocked by unpublished draft dependencies.
  This run used local Lake builds and official Lax static/inspection phases;
  it did not rerun independent kernel replay or obtain Archive acceptance.

## Local preview and exact next action

[Open the proof network](http://localhost:8138/lax-842588/#proof-network).
The URL was opened through the OS, and the preview server is running.

- Preview data is in `../migration-tools/trees-interface-preview/`, with
  current inspector reports and hashes of every local source/module artifact.
  It has no capture or local-build acceptance metadata. The repository's
  previous `build-output.json` remains historical; use this dedicated preview.
- The official Lax renderer receives the corrected canonical and RAM/Turing
  local draft outputs in memory. No Archive record is changed. The preview
  homepage and local dependency homepages explicitly identify local drafts.
- HTTP/HTML and embedded network checks passed: all ten concept pages exist,
  all nine local statements are proven, all nine local proofs have zero
  outstanding assumptions, and the canonical RAM page references `Lax808846`.
  See `../migration-tools/trees-interface-preview-verification.json`.
- A user-reported graph rendering failure is now fixed in the generated local
  preview assets. The renderer rounded fixed ports to 0.001px independently
  of the node envelope, so e.g. `100.016 > 100.01599999999999` triggered a strict
  bounds error. The envelope now includes the rounded port coordinates;
  port positions and the strict geometry validator are preserved.
  `../migration-tools/graph-port-envelope-fix.mjs` applies after each render,
  without modifying the installed renderer or mathematical submission data.
- The regression reproduces the original error and passes 3000 fractional
  geometry cases plus four real graph views. Isolated headless Chrome
  152.0.7977.84 checks all eleven tree pages / thirteen graphs without page
  errors. The proof-network screenshot matches the original successful
  Chromium rendering; the original failure depends on browser font metrics.
  Tests and screenshot: `../migration-tools/graph-port-envelope-test.log`,
  `graph-preview-browser-after.json`, and `graph-preview-after.png`.
  In-app browser automation still has a missing installed service path;
  the isolated browser test provides actual rendering verification.
- Source changes are uncommitted for review. Nothing was submitted or registered.

To regenerate after another successful local build, from the workspace root:

```sh
node migration-tools/trees-interface-preview.mjs
node migration-tools/serve-trees-interface-preview.mjs
```

**Next action:** wait for the user's review of the local preview before any
submission. Draft dependencies still prevent normal Archive publication.

## Earlier completed RAM model correction

Updated 2026-09-16. The user requested rebasing the submissions on
[`Lax808846.Ram`](https://laxarchive.org/lax-808846/Lax808846.Ram.html).
The previous Lean-version migration and publication record below describes
the earlier source, not validation of this correction.

## Implemented

- Public tree runtime witnesses are now programs for `Lax808846`, through
  the corrected canonical `RamComputableWithinUsing` predicate.
- `CheckedRamAdapter` applies the checked instruction embedding from
  `Lax759944Proofs.LegacyRamBridge`. It preserves the supplied input and output
  lists, word width, and workspace layout. The terminal instruction contributes
  at most one additional instruction; increasing each existential time
  coefficient by one covers that charge, including the computable uniform
  MSO coefficient. All public input and word-resource bounds are unchanged.
- The existing IMP compiler and expanded implementation theorems use the
  vendored `Lax759944Proofs.Legacy` definitions as a proof-side intermediate.
  The deleted `lax-865980` package is no longer their intended dependency.
- Both automaton wrappers and the uniform/fixed-sentence MSO wrappers use
  the checked embedding. Regression references now use the vendored namespace.
  The proof root imports `CheckedRamAdapter` explicitly.

## Dependency release pins

- The proof package now pins `Lax759944Proofs` to RAM/Turing commit
  `7010243df12cdda03abc5f63ec8de2c0963d4052`. That revision passed full local
  Lax validation and independent kernel replay: seven concepts and four
  annotated proofs, whose assumption lists are all empty. The commit is pushed.
- All three canonical concept/proof requirements now pin
  `8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b`. That revision passed full Lax
  validation and independent kernel replay: 12 concepts and 18 annotated
  proofs with empty assumption lists, in 7m08s. The commit is pushed, but its
  Archive draft update failed at the dependency gate: the remote validator
  rejects draft `Lax759944` and `Lax759944Proofs` dependencies. That revision
  has not been published. The local tree checks below used the corrected
  local sources through explicit package overrides.
- The MSO-word dependency remains
  `b7b157e93741492b33a0fa84ec76e24a571e2a98`; the public RAM model remains
  `Lax808846` at `9394e531cc51cb67a0214bca3f9264dfe97ba5c7`.

## Validation and exact next action

- The instruction embedding and its edge-case regressions pass Lean 4.33
  checking in the RAM/Turing submission; its axiom audit contains only
  `propext` and `Quot.sound`.
- `CheckedRamAdapter.lean` independently compiles with Lean 4.33 against that
  checked bridge. Its temporary output is `/private/tmp/CheckedRamAdapter.olean`.
- The local Lake build also passes for `CheckedRamAdapter` and both public
  tree statement modules. The adapter axiom audit reports only the permitted
  background axioms; see `../migration-tools/trees-808846-adapter-audit.log`.
- `CertifiedRepresentations.lean` and `CertificateReport.lean` both pass
  against the explicit local correction overrides; see
  `../migration-tools/trees-808846-certification.log`.
- `ArrayInput.lean`, `IntrinsicCompilerBridge.lean`, and
  `TreeAutomataEquivalence.lean` also pass with the corrected local overrides.
  Logs: `trees-808846-array-input.log` and `trees-808846-early-regressions.log`
  in `../migration-tools/`.
- `PrimitiveRecursiveAutomata` builds and `PrimitiveRecursiveBridge.lean`
  passes; see `../migration-tools/trees-808846-primitive-regression.log`.
- The selected endpoint build passes (3198 jobs), including all three edited
  public proof modules and all four rebased runtime theorems. Log:
  `../migration-tools/trees-808846-endpoints.log`.
- All eight implementation/equivalence regressions now pass. The remaining
  four were `IntrinsicPublicCompiler.lean`, `IntrinsicParameterBounds.lean`,
  `FixedSentenceModelChecking.lean`, and `RamComplexityStatements.lean`.
  They check exact public statement types and the expected axiom sets. Logs:
  `trees-808846-public-compiler.log` and `trees-808846-endpoint-regressions.log`
  in `../migration-tools/`.
- The full `Lax842588Proofs` root build passes (3222 jobs), including every
  retained helper module. Log: `../migration-tools/trees-808846-full-proof.log`.
- The final-source local proof build passes all 3222 jobs in 47m12s with the
  explicit dependency overrides; see
  `../migration-tools/trees-808846-local-final-build.log`. The concept root
  `Lax842588` also passes (960 jobs, 11.6s), logged in
  `../migration-tools/trees-808846-local-concepts.log`.
- The fresh annotation audit passes for all 15 tree proofs and the four
  canonical proofs that discharge their encoding assumptions. It checks
  current declaration kinds, exact statement types, and exact non-background
  axiom sets: nine tree proofs have empty sets, six use the four canonical
  statements, and all four canonical discharge proofs have empty sets.
  The final log names all 19 checked proofs; the logging-only rerun passes
  in 18.7s. Log: `../migration-tools/trees-808846-final-audit.log`.
- Stock Lean 4.33.0's kernel checker passes in 29m31s (exit 0) in the same
  Lake environment:

  ```sh
  env LEAN_NUM_THREADS=2 lake --packages=../../migration-tools/ram-808846-local-overrides.json env leanchecker --verbose Lax842588 Lax842588Proofs
  ```

  This single replay covers exactly both package prefixes: ten concept
  modules and their root, plus 161 proof modules and their root (173 unique
  modules, with no missing or extra modules against the source inventory).
  The separate checker log is `../migration-tools/trees-808846-local-kernel.log`.
  All 179 source/configuration file hashes match before and after validation;
  the snapshots are `trees-808846-validated-source-hashes.json` and
  `trees-808846-validated-source-hashes-after.json` in `../migration-tools/`.
  This is direct local proof validation, not Lax or Archive validation.
  These local commands require the explicit `--packages` override shown
  above. Ignored `lake-manifest.json` cache files still contain the retired
  dependency and are superseded by that override; ordinary Lake commands
  need regenerated manifests before use. The tracked source and lakefiles
  no longer depend on the retired package. No manifests were regenerated
  during the final validation.
- **The user chose to keep the submissions as drafts and declined registration.**
  No registration or further Archive publication will be attempted. There is
  no outstanding approval request. The canonical dependency pin remains
  `8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b` even though the Archive rejected
  that draft update.
- **Exact-pin Lax validation/replay of this correction cannot run against the
  unaccepted canonical revision.** The earlier successful Lax replay recorded
  below applies to the previous published source. The current local builds,
  regressions, and completed direct kernel replay must not be represented
  as acceptance by the Archive or as completion of the blocked Lax pipeline.
- The commit containing this record is the locally validated correction on
  branch `lean-4.33`. No local proof-validation work remains. The workspace
  `../RAM_808846_REBASE_STATUS.md` records its final commit and push status.
  The public Archive draft remains at the earlier revision recorded below.

## Earlier Lean 4.33 draft migration (historical)

Updated 2026-09-15. Original draft lax-53; new independent draft lax-842588
on branch lean-4.33. The abstract links to the original; no supersedes claim
or registration. Published at https://laxarchive.org/lax-842588/.

All local validation passed:
- Full proof build: 3218 jobs.
- Full Lax validation: 38m17s, including independent kernel replay 37m53s.
- Statement inspection: 10 concepts and 15 annotated proofs.
- Both MSO runtime headlines have empty assumption lists. Nine proofs are
  directly assumption-free; six auxiliary proofs refer to four canonical
  encoding concepts, all discharged by assumption-free proofs in the published
  dependency lax-560851. No unresolved mathematical assumptions remain.
- Full structural certification and certificate report pass.
- PrimitiveRecursiveBridge, ArrayInput, IntrinsicCompilerBridge,
  IntrinsicPublicCompiler, IntrinsicParameterBounds, FixedSentenceModelChecking,
  RamComplexityStatements and TreeAutomataEquivalence regressions pass.
- All ten concept files exactly match the original published source after
  namespace renaming. Test changes only adjust expected axiom-message wrapping.

Dependencies pin published Lean 4.33 drafts lax-146103, lax-560851 and
lax-759944, and registered word-RAM lax-865980. Lax reports 349 informational
warnings: two proof-package dependencies, four draft-package dependencies and
343 unused helpers. The inherited helpers and bespoke alternative compiler
modules are intentionally retained, as required by WORKFLOW.md.

Publication completed: archive issue 115, source commit
828f03cc85308eb60ba345b0c815310157600f70. Archive rebuild 23m27s;
public record written in 57s. All six Lean 4.33 migration drafts are published.
No remaining migration work. No registration performed.

Logs: ../migration-tools/trees-*.log. Original draft and main are untouched.

## Historical record from the original (not validation of this port)

# Lax-53 current state

Updated: 2026-09-07. Validated and submitted as the public Lax-53 draft.
The public RAM statements now use Lax-58's reusable
`RamComputableWithinUsing` predicate. Their encodings, algorithms, bounds, and
quantifier order are unchanged: the concise proofs unfold the predicate and
invoke the previously proved expanded implementation theorems. The two
automata/MSO directions share `MSOTreeAutomataEquivalence.lean` with the
equivalence statement.

## Implemented versus unfinished

- Structural encoding boilerplate is replaced by four certified derivations
  in `concepts/Lax842588/StructuralRepresentations.lean`: terms, relations,
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
  `env LEAN_NUM_THREADS=2 lake build Lax842588Proofs` (3156 jobs, session `12059`).
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
  http://localhost:8126/lax-842588/. Verified the combined equivalence concept and
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
  concern discouraged proof dependencies, draft dependencies, and Lax865980's
  successor; none is a build or proof failure.

## Publication

The validated source is public at `https://github.com/szymtor/lax53` and is
bound to control issue 53. The Archive rebuilt the submitted commit in 21m56s,
wrote the public record, and published the replaceable draft at
`https://laxarchive.org/lax-842588/`. The submission is deliberately not registered.

The dependency mismatch is resolved: Lax560851 and Lax560851Proofs pin the published
`szymtor/lax58@83d795f06ae20b48ceed34a9f1284975d305b9c4`; Lax62Proofs is no
longer required. `Lax842588Proofs.ArrayInput` contains only the old Lax865980 reader
and supporting proofs, with upstream attribution. The concepts and public RAM
model did not change for this localization. The subsequent concept consolidation
was separately requested by the user.

Warnings from standard validation are informational: two proof-package
dependencies, three draft-package requirements, and Lax865980 having a successor
(Lax67). They did not fail the build. Previous interrupted attempts and the
exact provenance of the localized reader are recorded in `SESSION_HISTORY.md`.

Two package `.DS_Store` files remain recoverably moved to
`/private/tmp/lax53-layout.gqgzSe/`. Preserve the extensive dirty worktree.

Workflow: [WORKFLOW.md](WORKFLOW.md). History: [SESSION_HISTORY.md](SESSION_HISTORY.md).
