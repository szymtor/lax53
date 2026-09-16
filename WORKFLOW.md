# Lax-53 implementation workflow

Read [CURRENT_STATE.md](CURRENT_STATE.md) first. Keep Lax-58 limited to neutral
structural encodings and its arena; charged compiler refinements belong here.
Use intrinsic Lax-52 formulas directly, not a second serialized syntax.

## Public interface after the nine-claim cleanup

The public claims are determinization; both MSO/automata directions and their
equivalence; finite value translations; tree and sentence round-trip laws;
uniform automaton acceptance; and uniform MSO model checking.

Keep formula/tree structurality, both input-length facts, and both
fixed-parameter runtime results as ordinary proof-package lemmas. Abstract
complementation uses the public determinization statement; equivalence uses
the public directional statements. The fixed-automaton helper specializes the
public uniform acceptance statement. The tree-only fixed-sentence helper
retains its checked direct implementation; a generic input-specialization
lemma is outside this cleanup.

The final release uses exact Archive pins for the registered word-MSO,
canonical-encoding, RAM/Turing, and dedicated-input/output RAM dependencies.
Full Lax validation has regenerated both package manifests, so ordinary Lake
commands now use those pins without development overrides. Do not replace the
ignored manifests by hand. The user reviewed the nine-claim local preview and
then explicitly authorized submission and permanent registration on 2026-09-16.
Future mathematical changes to the registered source require a new submission.

## Accepted simplification: generic execution bridge

Keep the approved concepts and certified input unchanged. Build a proof-side
realization of primitive-recursive programs in the existing bounded IMP+
semantics, then use the verified IMP+-to-RAM compiler. The parameter-only
compiler may have very large computable time and word bounds; the tree
evaluator must retain linear dependence on tree size.

The acceptance sequence is:

1. Finite seven-constructor code with exact `Nat.Primrec` semantics.
2. Charged pairing/unpairing and structural code-to-IMP+ compilation, including
   scratch-register preservation and computable bounds.
3. A complete realization of an existing operation (`inter_prim`), not just
   an existential pure code or an unchecked evaluation example.
4. Runtime translation of the certified formula arena into private internal
   data, full compilation, and materialization for the existing evaluator.
5. Computable parameter-only bounds, uniform model checking, and its
   fixed-sentence companion.

Steps 1–5 now have Lean proofs, including actual RAM intersection, the complete
public-input model checker, and both runtime results. The uniform
program chooses its compiler/layout before runtime inputs and charges arena
reading, full formula compilation, materialization, and evaluation. Its
parameter-only coefficients discharge the lower-level resource premises.
The fixed-sentence companion receives only the tree and materializes a fixed
automaton from its program instructions during the counted run. Current
validation results and the separate Archive gate are in `CURRENT_STATE.md`.
For composition, use the underlying `compile` IMP body and its register/array
frame theorem, not the standalone RAM wrapper's extra `read` and `write`.
The typed bridge emits `encode (some result)`; the output adapter must
account for that tag before unpacking the flat list. This composition is now
proved by `IntrinsicCompilerMaterialize.materialize_exact_spec` and
`exists_tableCompiler`: reuse the body rather than reconstructing the wrapper.
Use `ArenaFieldAccess.load_spec` for constructor-field reads; its `atPath`
premises must reduce against the generated structural encodings. Zero unused
row fields so the working data contains only the intended primitive content.
`IntrinsicFieldExtraction.packedProgram_spec` now combines the checked
paths, runtime constructor dispatch, and register-only row packing. Use
`IntrinsicOccurrenceInput` to connect it to the existing postorder loader;
that composition now builds and passes focused regressions and replay. The
backward scan in `IntrinsicFormulaInput` prepends each row directly to an
accumulator; it needs no additional row array. `IntrinsicAlphabetInput`
packs the existing table prefix including its length header and removes
that header by charged unpairing. `IntrinsicCompilerFromArena.exists_compiler`
composes these adapters with compilation and exact table materialization.
`IntrinsicCompilerPrepare` now establishes its `Ready` premise from the public
input. `IntrinsicCompilerFrame` preserves the arena and tree pointer through
compilation. `IntrinsicEvaluatorPrepare` reads the retained tree and initializes
the evaluator header without reading another tape word. `IntrinsicModelChecking`
composes the complete IMP body and proves initialization from zero arrays;
`IntrinsicModelCheckingRam` applies the instruction-level transfer.
Use `ImpLayout.exists_layout` for the complete finite program's input-independent
layout; no additional hand-maintained global register inventory is needed.
The explicit resource premises are now discharged by the envelopes in
`IntrinsicParameterEncoding`, `IntrinsicCompilerParameters`,
`IntrinsicCompiledTableBounds`, `IntrinsicTimeBounds`, and `IntrinsicWordBounds`.
Reuse these proofs. They use computable finite-prefix maxima and do not
assume `budget c` monotone. `FixedSentenceModelChecking` supplies the separate
tree-only theorem using `FixedTableLoader` and the same evaluator.
Packing source
registers requires the destination to be distinct from every source.
Do not assume an
arbitrary Lean evaluator executes as a RAM instruction. Numeric intermediate
codes are proof-private and built at runtime, never an alternate public
input convention or supplied advice. Preserve the existing bespoke proof
modules while validating the replacement strategy.

## Existing bespoke compiler operation completion contract

For each operation, fill in this evidence checklist before calling it done:

- Pure result: name the exact `AutomatonCode` and language-correctness theorem.
- Program: give the concrete IMP+/RAM program, including all enumeration,
  materialization, allocation, and descriptor work performed at runtime.
- Preconditions: state word-fit, capacity, register, input, and storage bounds.
- Representation: prove exact transition/accepting heap prefixes and output
  descriptor, preserving the prior stack/heaps and unrelated machine state.
- Cost: prove a concrete instruction bound for the whole lifecycle; later
  composition must sum traversal, construction, storage, and evaluation costs.
- Composition: connect the operation to the actual formula compiler step.
  A subautomaton component alone is not a completed formula constructor.
- Validation: record the focused module build, downstream check, and remaining
  assumptions. A file compiling is not evidence that a missing theorem exists.

Reuse `AutomatonBuildStartReady`, `BuiltAutomaton`,
`BuiltAutomatonPushReady`, `beginCompiledAutomaton_spec`, and
`pushBuiltAutomaton_spec` in
[MSORamCompilerBuild.lean](proofs/Lax842588Proofs/MSORamCompilerBuild.lean).
Reuse `CompilerStackRep`, `TransitionHeapRep`, and `AcceptingHeapRep` rather
than introducing another storage contract for each operation.

## Existing bespoke route (preserved; not the active next task)

| Milestone | Current evidence / missing work |
| --- | --- |
| Pure intrinsic compiler | `compileFormulaForRAM_correct` in [IntrinsicFormulaPostorderCompiler](proofs/Lax842588Proofs/IntrinsicFormulaPostorderCompiler.lean) is proved. |
| Shared lifecycle and row writers | Build/push contracts, empty construction, and binary/radix materialization are implemented. |
| Somewhere atomic components | `compileEqualAtomicAutomaton_spec`, `compileLabelAtomicAutomaton_spec`, and `compileMembershipAtomicAutomaton_spec` in [MSORamCompilerSomewhere](proofs/Lax842588Proofs/MSORamCompilerSomewhere.lean) are proved. These are not the full formula atomic steps. |
| Charged sparse-valid construction | Pure `sparseValidCodeP` and semantic equivalence exist in [SparsePrimitiveAtomicAutomata](proofs/Lax842588Proofs/SparsePrimitiveAtomicAutomata.lean); the bespoke RAM lifecycle and cost remain unfinished. |
| Charged intersection | Combine valid markings with a somewhere component to finish a first nontrivial formula atomic step. |
| Edge and closure operations | Implement charged edge construction, union, complement, determinization, and projection; tie each to the pure compiler. |
| Full postorder compiler | Compose traversal and all constructor steps, prove exact output and total instruction bound. |
| Headline runtime theorems | Completed via the active generic bridge and fixed-table specialization, not the unfinished bespoke operation chain. |

Do not move pure formula compilation outside the measured uniform execution.
Fixed-sentence specialization can isolate sentence-dependent work only as
permitted by that theorem's actual input/cost specification.

## Validation and certificate inspection

From this repository root:

```sh
bash scripts/check-certified.sh
bash scripts/certificate-report.sh
```

The report builds current structural concepts first and prints all four
encoders, full law propositions, witness definitions, and axiom dependencies.
Proof bodies are hidden for readability; use `--proofs` to expose them.
The displayed printer output is never input to certification. For a review
diff, save the report before and after the change and compare the two files.

For a compiler change, first build the named module and its immediate consumer
from `proofs/` (for example `lake build Lax842588Proofs.MSORamCompilerRadixWord`).
For the active generic bridge, use `bash scripts/check-primitive-recursive.sh`
from the repository root. It includes source-semantics checks, bounded/RAM
recursion examples, intersection compatibility, and explicit axiom guards.
Use `bash scripts/check-intrinsic-compiler.sh` for the full internal compiler,
flat-table output, packing/unpacking, and materializing-body checks. These are proof-side
interfaces, not a substitute for public-arena end-to-end execution.
The internal one-word RAM theorem is not the public theorem. The public
composition is now separately checked by `tests/IntrinsicPublicCompiler.lean`;
its explicit premises are not a substitute for the headline parameter bounds.
`tests/IntrinsicParameterBounds.lean` and `tests/FixedSentenceModelChecking.lean`
check the uniform public type, the fixed-sentence helper's tree-only type,
and their background-only axiom sets.
The word coefficients cover the RAM layout span as well as IMP values.
At an integration milestone, from `proofs/`:

```sh
env LEAN_NUM_THREADS=2 lake build Lax842588Proofs
```

Use bounded Lean concurrency; do not launch several full builds of the same
package at once. Run full Lax validation/replay once archive dependencies are
resolvable. Record archive failures separately from local Lean results.

The Lax865980 array input helper now lives in `Lax842588Proofs.ArrayInput`, localized
with attribution from the old Lax62 harness. Do not restore the Lax62 dependency:
its current reader uses a different RAM model. `check-intrinsic-compiler.sh`
also checks this helper's syntax, cost, frame properties, and axiom set.
The two MSO/automata directions and their equivalence share the single concept
`MSOTreeAutomataEquivalence`; their proof modules remain separate. After changing
this concept, run `lake env lean ../tests/TreeAutomataEquivalence.lean` from
`proofs/` to check all three proof types against the consolidated statements.

Before a session ends, refresh `CURRENT_STATE.md` with completed checks,
unproved statements, blockers, and one exact next action. Append detailed
history to `SESSION_HISTORY.md`; do not grow the current summary into a log.
