# Session history

Historical checkpoints, preserved from the former `FORMALIZATION_STATE.md`.
Read `CURRENT_STATE.md` for authoritative current status; later audit entries
can supersede earlier claims in this history.

The following sections retain the earlier handoff and chronological log.

## Submission

- Lax id: `lax-842588`
- Lean namespace: `Lax842588`
- Proof namespace: `Lax842588Proofs`
- Working title: `MSO-automata-trees`
- Current phase: implementing the charged distinguished-arena RAM frontend
  and the stronger uniform intrinsic-sentence model-checking theorem

## Intended result

Extend the MSO syntax and semantics of `lax-52` from finite words to finite
ranked trees. Define ranked alphabets, ranked trees, their relational
structures, bottom-up finite tree automata, runs, acceptance, recognizable
languages, determinism and determinization, and the equivalence between
tree-automaton recognizability and MSO definability.

The user confirmed the following semantics:

- There are no leaf states. The transition rule applies uniformly to every
  node, including rank-zero symbols, whose transitions have the form `(a,q)`.
- The relational tree signature has unary label predicates and binary indexed
  child relations through the maximum rank; it has no ancestor relation.

## Decisions and invariants

- The project was initialized with `lax init .` on 2026-08-10.
- `lax print instructions` and the complete `lax print spec` were read before
  authoring Lean.
- Concepts must be polished and validated with `lax build . --only concepts`,
  then presented to the user for semantic review before proof work.
- Generated `build-output.json`, `lake-manifest.json`, `.lake/`, and package
  override files remain untracked as required by the Lax specification.
- Registration is never performed by the agent.

## Session log

### 2026-09-04 audit response

- Replaced the insufficient implication “derived presentation is injective,
  therefore advice-free” by first-class `FormulaStructureLaws` and
  `TreeStructureLaws`. The formula certificate pins every formula constructor
  as well as term variables, relation symbols, finite term families, and
  finite indices; the tree certificate pins its symbol payload and all
  recursively represented children. Both generated folds satisfy the laws by
  kernel-checked reduction.
- Kept Lax-58 `FieldEncoding` explicitly low-level: it drives elaboration but
  confers no structurality status. Moved ordinary presentation helper theorems
  from Lax-58 concepts into `Lax560851Proofs`. Full Lax-58 validation passes four
  concepts and fifteen proof conclusions.
- Moved the proof-private evaluator layout from the forbidden
  `Lax842588.TreeModelCheckingEncoding` namespace to `Lax842588Proofs`, added its exact
  direct root import, and moved `proofs/RadixScratch.lean` to the workspace
  `tmp/` scratch directory.
- Added a direct Lax-58 concept dependency to the Lax-53 proof package and
  proved the previously omitted `automatonInput_length` public statement.
- Thirteen of the fifteen current Lax-53 axioms now have annotated proofs. The
  two remaining statements are exactly the genuinely unfinished uniform MSO
  runtime theorem and its fixed-sentence specialization.
- Reconciled both abstracts, the Lax-58 proposal/state file, and the
  cross-repository handoff with the current four-module interface and the
  unfinished headline theorem.

### 2026-09-03

- Renamed the mathematical translation concept from
  `EffectiveTranslations` to `ValueTranslations` and its conclusion to
  `language_equivalence`. The words “effective” and “uniform” were removed
  from this interface because it asserts only language-preserving functions
  between mathematical values; computability and execution belong to the RAM
  results. The supporting proof module is now `TranslationConstructions`.
  `lake build Lax842588` and the focused value-translation proof build both pass.
- The user fixed the final MSO contract: one RAM program is chosen before the
  alphabet, intrinsically scoped sentence, ranked tree, and word width. Its
  distinguished input represents the dependent triple `(alphabet, sentence,
  tree)`, and it decides sentence-language membership.
- Formula-to-automaton compilation, if used, must execute inside that same RAM
  run and be included in its instruction bound. The uniform automaton/tree
  evaluator is an internal verified backend. Fixed-sentence linearity will be
  stated only as a companion specialization of the stronger uniform result.
- Added semantic arena-address/representation lemmas, a verified charged
  arena loader, a verified instance-opening phase, and the fixed IMP+ frontend
  that begins decoding the certified automaton/tree arena into the existing
  evaluator's proof-private working layout. The alphabet body, counted loop,
  loop exit, and complete header-initialization phase now compile with explicit
  Lax-13 instruction budgets. A local operational lemma proves every IMP+ run
  preserves array lengths, allowing workspace capacity to be carried between
  charged phases. The fixed automaton-body opener also compiles: it obtains the
  state count and certified transition/accepting-list cursors and writes the
  state-count header.
- The transition frontend now explicitly zero-fills missing child-state slots
  in its fixed-width proof-private records. Consequently malformed short
  transitions are represented according to `List.getD` independently of the
  scratch array's previous contents; no implicit zero-memory assumption is
  needed for record correctness.
- Verified the charged body for one represented transition-child list cell.
  Its invariant tracks the certified suffix cursor, the exact number of
  children consumed, the first `R` materialized child-state words, and
  preservation of the table prefix. Truncation preserves the full arity
  count, and the proof is now imported by the proof root.

### 2026-09-02

- Replaced the specialized public automaton-table/postorder input with the
  distinguished Lax-58 input of the complete named structural value
  `automatonAcceptance(automaton, tree)`. Its physical form is exactly the
  root followed by the dense three-word arena.
- Replaced the former `RunsTo` wrapper statements with direct
  `Lax865980.RamComputes.ComputesInTime` statements. The uniform theorem chooses
  one program and constant before the automaton, tree, and word width; a
  separate fixed-automaton theorem makes its different quantifier order and
  non-effective specialization status explicit.
- Kept the fixed-sentence theorem at the mathematical translation boundary:
  one uniform evaluator consumes the translated automaton/tree arena, and no
  formula serialization or uncharged runtime preprocessing appears.
- Added `IMPLEMENTATION_NOTES.md`, recording removed serialization modules,
  the exact input format, quantifier orders, fixed-parameter convention, and
  local proof helpers that may merit later extraction.
- Updated the Lax-13/Lax865980Proofs pins to registered commit `92ae2d6...`.
  Inspection confirms that Lax-62 contains the higher refinement/autoref
  tower, while the concrete IMP+, compiler, simulation, and transfer modules
  used by the direct proof remain in `Lax865980Proofs`; no Lax-62 dependency is
  currently required.
- `lake build Lax842588` succeeds through 910 jobs against the current Lax-13
  checkout and the local Lax-58 override. A source audit finds no machine
  tags, offsets, pointer arithmetic, IMP+ syntax, or compiler code in the
  revised runtime concept files.
- Rechecked full concept validation with local Lax CLI `0.1.33`. Its
  resolution phase still requires a content-bearing Archive record before its
  later Lake provisioning phase reads package overrides, so
  `lax build . --only concepts` rejects the unsubmitted Lax-58 dependency.
  The generated override itself correctly points to
  `canonical-encodings/concepts`, and direct Lake compilation uses it. This is
  a limitation of the installed validator path, not a Lean dependency error.
- Per `AGENTS.md`, proof edits are paused until the user reviews this exact
  concept surface.

- Implemented the reviewed Lax-58/Lax-53 boundary. Lax-53's mathematical
  equivalence now quantifies direct value-level translations between finite
  automaton data and intrinsically scoped formulas; it no longer mentions
  binary serialization or an existential codec package.
- Added `StructuralRepresentations.lean`. It gives explicit named structural
  presentations for ranked alphabet codes, transitions, automata, formulas,
  sentences, and ranked trees using the fixed Lax-58 vocabulary. Three grouped
  certificate statements assert combinator lawfulness, complete formula
  constructor equations, and complete ranked-tree constructor equations.
- Tightened the ranked-tree representation after review: the unique tree
  constructor uses the symbolic name `"node"`, while the symbol number is an
  explicit `Nat` field and children occur recursively in their finite-index
  order. Raw-formula equations likewise use symbolic constructor names; the
  certificate statements now contain neither numerical tags nor `Raw.pair`
  layout.
- Added and compiled proofs for all structural certificate statements and the
  two value-level translation directions.
- Removed the obsolete formula token serializer/parser and its coding-specific
  computability proof modules. Retained numeric finite-automaton operations
  because they implement the reverse compiler and the RAM evaluator.
- Revised `MSOLinearTime`: the sentence is fixed outside the measured
  execution, so preprocessing is uncharged; runtime-input preprocessing would
  have to be included. The public theorem does not impose an unrelated hidden
  formula coding merely to state `Computable`.
- `lake build Lax842588Proofs.MSOLinearTime` succeeds through 3022 jobs, and the
  final `lake build Lax842588Proofs` succeeds through 3038 jobs after root-import
  cleanup. `lake build Lax842588` succeeds through 909 jobs.
- Removed the two large commented remnants of the former raw-formula token
  serializer and parser. A source audit finds no `sorry`, `admit`, or proof-
  package axioms, and no active formula serialization API.
- Added the declared Lax-58 dependency and generated local Lake override. The
  installed Lax CLI still rejects the dependency during Archive resolution
  because Lax-58 has no content-bearing record; direct Lake builds honor the
  local override. Do not publish solely to bypass this tooling mismatch.
- Committed the completed Lax-58 rewrite as
  `0994f68f21d33c6a065fd3bb4578b4bd9efb8e96` and updated the declared Lax-53
  dependency pin to that exact commit before checkpointing Lax-53.
- Added `CROSS_REPO_HANDOFF.md` as the durable handoff for reopening the
  parent `laxSubmissions` directory as one writable Codex workspace. It records
  both repositories' Git states, the uncommitted Lax-58-dependent Lax-53
  concept draft, the agreed simplified Lax-58 architecture, preservation
  requirements, the publication blocker, and the exact continuation sequence.
- After the checkpoint commits, revalidated the revised symbolic-constructor
  client against the live local Lax-58 checkout. `lake build Lax842588Proofs`
  succeeds through 3038 jobs. The declared Lax-58 Git pin remains the clean
  checkpoint `0994f68...`; the generated local package override intentionally
  supplies the subsequent uncommitted Lax-58 refinements during coordinated
  development.

### 2026-09-01

- Began the user-requested refactor of the effectiveness layer to use the
  generic codec vocabulary from `lax-58` instead of exposing a hand-written
  prefix formula parser and constructor tags.
- The proposed `EffectiveTranslations` concept now treats raw formulas as
  inductive syntax, existentially chooses canonical and effective codecs for
  automaton bodies, alphabet--automaton inputs, and alphabet--sentence inputs,
  and states both translations using `Lax560851.CanonicalCodec.Codec.ComputableMap`.
- Kept the fixed-width natural-word automaton table only in
  `TreeModelCheckingEncoding`: its layout is intrinsic to the constant-time
  random-access algorithm and its runtime bound, not the generic
  serialization. Formula preprocessing no longer exposes a word layout.
- Updated the MSO linear-time concept so effectiveness of compilation and of
  its coefficient is expressed through the same hidden serialization.
- The changed concept modules were syntax-checked successfully against the
  locally built `lax-58` artifacts without changing Lake's generated manifest.
- Blocking validation fact: `lax-58` is still in Archive state `init`, has no
  source record and no Git remote, so `lax-842588` cannot yet add the required
  Archive-pinned dependency or run an ordinary Lax concept build. The next
  action after concept review is to publish `lax-58` as a draft, pin its exact
  source in both `lax-842588` packages, and only then adapt the proofs.

### 2026-08-31

- Completed and verified the uniform IMP+ bottom-up evaluator, including
  fixed-width automaton-table decoding, postorder stack evaluation, the
  accepting-state scan, and transfer to the archive word-RAM.
- Proved one fixed RAM program decides encoded automaton acceptance within
  `C (|M| + 1)^2 |t|`; the concrete proof uses the conservative absolute
  witness `C = 1000000`.
- Stated the MSO runtime result with its necessary preprocessing boundary:
  the uniform computable MSO compiler first produces an encoded automaton,
  after which the same fixed RAM evaluator runs in linear tree time. The
  resulting sentence coefficient is proved computable.
- Source audit finds seven concept axioms and exactly seven annotated proof
  conclusions, with no `sorry` or `admit` in the concept or proof sources.

### 2026-08-30

- Completed a total uniform MSO-to-automaton compiler on arbitrary formula
  strings. A primitive-recursive syntax guard rejects malformed strings; a
  bounded stack compiler handles canonical encodings; and the wrapper was
  proved equal to the previously verified semantic compiler.
- Proved primitive recursiveness, hence computability, of the syntax guard,
  bounded compiler, pullback wrapper, and full encoded translation. Connected
  this with the existing computable automaton-to-MSO direction, so
  `EffectiveTranslations.uniform_effective_equivalence` is now an annotated
  proof recognized by Lax.
- Found and corrected a semantic defect in the physical model-checking input:
  the postorder tree suffix had no length or terminator, while an exhausted
  Lax word-RAM input tape halts rather than reports EOF. Both the parameter and
  tree are now length-prefixed blocks. This adds one input word but leaves
  `treeSize` unchanged.
- Updated the abstract to say that the uniform effective translations are
  proved and preserve the represented alphabet and language.
- `lax build . --no-color` passes (`11 concepts · 5 proofs`). The only
  remaining unproved concept conclusions are the uniform word-RAM automaton
  evaluator and its MSO consequence.
- `lax sync` updated the local archive from 25 to 28 submissions. A refreshed
  preview is running at `http://localhost:8125`.

### 2026-08-10

- Reserved and scaffolded `lax-842588`.
- Confirmed the authenticated Lax account is `szymtor`.
- Read the authoring instructions and specification.
- Added this durable state file and `AGENTS.md` as the next-session entry point.
- Initialized a local Git repository and created initial commit `212ae23`.
- Verified the untouched concept package with
  `lax build . --only concepts --no-color`; layout, dependency resolution,
  compilation, and statement inspection all passed.
- Read the intended scope from the user and inspected the neighboring
  `lax-52` concept source at pushed commit
  `93d9b7c3ad77b383b9734cede0b95bfd17928575`.
- Confirmed `lax-52` is still in the archive's `init` state, so `lax-842588`
  cannot yet resolve it as an Archive dependency.
- Identified the two semantic conflicts above before concept authoring.
- The user resolved both conflicts by choosing uniform rank-zero transitions
  and indexed child relations.
- Authored seven concept modules: finite ranked trees, relational tree
  structures, bottom-up tree automata, determinization, both directions of the
  MSO correspondence, and their combined equivalence.
- Refreshed the Archive and confirmed `lax-52` is a draft at pinned commit
  `93d9b7c3ad77b383b9734cede0b95bfd17928575`.
- `lax build . --only concepts --no-color` passed layout validation,
  dependency resolution, compilation, and statement inspection. Its only
  warning is that `lax-52` remains a draft dependency.
- In semantic review, renamed tree positions to nodes throughout and renamed
  the alphabet-wide child-index embedding from `ofFin` to
  `ofSymbolIndex` for clarity.
- A subsequent full `lax build . --no-color` passed with 7 concepts and 0
  proofs, and the running preview rebuilt successfully.
- Replaced the `WType` abbreviation with the domain-specific inductive
  `RankedTree.Tree.node`. Moved `ChildIndex`, `Node`, node labels, and the
  indexed immediate-child relation from `RankedTree` to `TreeStructure`.
- The full Lax build and live-preview rebuild passed after this refactor.
- Replaced the predicate `IsTreeStructure` and its unique-existence axiom with
  a direct canonical `treeStructure` definition whose relation map is given by
  node labels and indexed child edges. Simplified `TreeModels` accordingly;
  the full build and preview rebuild passed.
- Moved the tree-intrinsic API (`ChildIndex`, `Node`, labels, immediate-child
  navigation, and `TreeLanguage`) back to `RankedTree`. `TreeAutomaton` now
  imports only `RankedTree`; the logical `TreeStructure` dependency is confined
  to the MSO-facing modules. The full build and preview rebuild passed.
- Changed tree-automaton transitions and acceptance from `Prop`-valued
  predicates to `Bool`-valued tests, making these finite automata directly
  inspectable by future translation algorithms. Updated run, acceptance, and
  determinism semantics; the full build and preview rebuild passed.

### 2026-08-11

- The user approved exposing effectiveness as existential computable
  translations and explicitly authorized proceeding with proofs.
- Added `EffectiveTranslations.lean`. It gives a canonical numbered finite
  automaton code, its Boolean interpretation, and language-preserving
  `Computable` translation theorems in both directions under `Primcodable`
  assumptions. The concept build passed with only the expected draft
  dependency warning.
- Proved determinization by the standard finite powerset construction in
  `Lax842588Proofs/Determinization.lean`; the annotated conclusion is detected by
  Lax.
- Refined ranked-tree navigation: `Node.child` is now defined directly in the
  `RankedTree` concept and `Node.ChildAt` is the corresponding direct indexed
  relation. This matches the earlier decision that node navigation is
  tree-intrinsic and avoids a dependent-index ambiguity in the former
  inductive relation. The concepts and dependent proof modules compile.
- Added reusable node lemmas (`ChildAt` functionality and every non-root node
  has a parent) and generic derived MSO semantic simp lemmas.
- Completed `Lax842588Proofs/TreeAutomataToMSO.lean`. The constructed sentence
  existentially chooses one monadic set per state, enforces a state partition,
  checks every local ranked transition including rank zero, and checks the
  accepting state at the unique root. Its correctness is connected recursively
  to `Automaton.RunsTo`, and the annotated concept theorem compiles.
- Began the converse marked-tree construction. `MarkedTrees.lean` defines
  Boolean FO/SO tracks, represented valuations, marked semantics, variable
  projection maps, and empty marking/erasure. `TreeAutomataClosure.lean` proves
  closure under intersection, complement (via determinization), and union.
  The proof package currently builds successfully, with only an unused-section
  variable linter warning in the completed automaton-to-MSO proof.
- Completed recognizability of valid marked trees and all atomic MSO formulas.
  Added finite-automaton closure under Boolean operations and rank-preserving
  projection of the newest FO or SO marker.
- Proved that marker dropping preserves the underlying relational tree
  structure. Added explicit witness-decoration trees for first-order nodes and
  monadic node sets, together with node equivalences, structure equivalences,
  and preservation of represented valuations.
- Proved the semantic projection identities for both quantifiers and completed
  structural induction showing that every open MSO formula has a recognizing
  automaton over its marked alphabet.
- Added the zero-marker bridge: zero-marked trees are structurally equivalent
  to ordinary ranked trees, and automata over zero-marked symbols pull back to
  automata over the original alphabet. The annotated MSO-to-automaton theorem
  and the combined Büchi--Elgot--Trakhtenbrot equivalence are now implemented.
- The user explicitly requested that the two exposed effectiveness results be
  left without proofs. They are bundled as the single concept theorem
  `EffectiveTranslations.effective_equivalence`, documenting both computable
  directions while satisfying the preview's one-statement-per-concept rule.
  The completed proof scope is determinization plus both extensional
  translations and their equivalence.
- Final validation after cleanup: `lake build Lax842588Proofs` completed all 915
  jobs with no proof warnings, and `lax build . --no-color` passed layout,
  dependency resolution, concept compilation, proof compilation, and statement
  inspection (`8 concepts · 4 proofs`). The only remaining warning is the
  expected one that dependency `lax-52` is still a draft submission.
- Restarted `lax serve` outside the sandbox. Port 8123 was occupied, so the
  live preview is at `http://localhost:8124`; it reported a successful rebuild
  after the final concept build.
- The user subsequently reversed the decision to omit effectiveness proofs.
  The agreed architecture is to define explicit computable compilers between
  `FiniteAutomatonCode A` and the inductive MSO sentence type, prove language
  preservation using the completed extensional development, and only then
  derive functions on numeric/string serializations. Raw `Automaton A Q` is
  not a suitable computable input because its state type is heterogeneous and
  its transition table is represented as a function.

### 2026-08-13

- Before beginning effectiveness implementation, the user requested a uniform
  statement in which the ranked alphabet itself is input.
- Redesigned `EffectiveTranslations.lean` at concept level. A ranked alphabet
  is now a finite rank string `List Nat`, interpreted canonically with symbol
  type `Fin code.length`. Automata and raw MSO formulas use uniform numeric
  token strings, and the single theorem quantifies over compilers between
  alphabet-plus-body encodings while requiring the alphabet component to be
  preserved exactly.
- Raw MSO strings are prefix parsed and then scope/alphabet checked into the
  intrinsically scoped `lax-52` formula type. Malformed strings denote the
  empty language, keeping the language semantics and future compiler total.
- The revised concept module compiles directly. No effectiveness proof work
  has begun; the concept must be reviewed and approved first.
- The user approved both representation choices: `List Nat` is the abstract
  string format, and malformed MSO formula strings denote the empty language.
  The uniform effectiveness concept is therefore semantically approved. Do
  not begin its proof unless separately requested.
- Full `lax build . --no-color` passed after approval (`8 concepts · 4
  proofs`); the only warning remains the expected draft dependency on
  `lax-52`. This full build refreshes `build-output.json` for the live preview.
- Updated the submission authors, at the user's direction, to Szymon
  Toruńczyk and Codex 5.6, in that order.
- Added concept drafts for linear-time model checking on 2026-08-13. Reused
  the archive-standard word RAM `Lax865980.Ram` at registered commit
  `d35ba57ad420ce6a6d3c763aa7f6a4a8be1d406d`, rather than introducing a new
  cost model.
- `TreeModelCheckingEncoding.lean` uses a postorder tree word with one symbol
  number per node, so its length is exactly the number of tree nodes. Encoded
  alphabet–automaton and alphabet–formula parameters are self-delimiting
  blocks placed before the tree word.
- `AutomatonLinearTime.lean` states that one uniform RAM program decides
  acceptance in `P(|M|)·|t|` steps for a fixed polynomial `P` and complete
  encoded alphabet–automaton parameter `M`. `MSOLinearTime.lean` states the
  analogous `f(φ)·|t|` bound for a computable function of the complete encoded
  alphabet–sentence parameter.
- The word-length conditions follow the established Lax865980/Lax11 convention:
  input entries, addresses, and the claimed runtime must fit into `w`-bit
  words. Concept validation passes (`lax build . --only concepts --no-color`),
  with expected draft warnings for `lax-13` and `lax-52`.
- Ran `lax sync`; the local archive index updated successfully with 24
  submissions.
- A subsequent full `lax build . --no-color` passed layout, dependency
  resolution, concept compilation, proof compilation, and statement
  inspection (`11 concepts · 4 proofs`). The only warnings are the expected
  draft-dependency warnings for `lax-13` and `lax-52`.
- Restarted the live preview after that build. Ports 8123 and 8124 were already
  occupied, so the refreshed preview is available at
  `http://localhost:8125`; it includes `lax-842588` and 23 published submissions.

## Historical implementation notes

The user approved proof work for every remaining theorem and authorized
strengthening the automaton coefficient when concrete. The automaton concept
now states the explicit bound `C (|M| + 1)^2 |t|`; this compiles.

Proof work in progress:

- Added the pinned `Lax865980Proofs` dependency so the verified IMP+-to-word-RAM
  compiler can be used. Provisioning succeeded outside the sandbox.
- Added `Lax842588Proofs.EffectiveTranslations`: canonical raw-formula serializer,
  parser round-trip, and a concrete automaton-to-MSO compiler. Its elaborated
  formula is proved equivalent to accepting runs. A separate token-level
  implementation is proved primitive recursive and extensionally equal to
  the semantic compiler, completing the automaton-to-MSO half of uniform
  effectiveness (including alphabet preservation and language preservation).
- Added `Lax842588Proofs.EncodedAutomatonEvaluation`: a sparse pure evaluator and
  a complete proof that its reachable-state list is exactly
  `Automaton.RunsTo`, hence its Boolean result decides acceptance.
- Added `Lax842588Proofs.FiniteAutomatonEncoding`: a complete finite-table
  serializer, proved semantically exact. Its serializer is primitive recursive
  uniformly when the alphabet, state bound, transition test, and acceptance
  test all depend on an encoded input. This is the reusable bridge for the
  explicit finite automata in the reverse MSO translation.
- Added `Lax842588Proofs.EncodedAutomataOperations`: numeric lookup, state
  renaming, product/intersection, bitset determinization, complement, union,
  projection, and pullback definitions. State renaming, intersection,
  canonical powerset determinization, complement, and union now have complete
  semantic proofs. The powerset transition was tightened to require the
  canonical `Encodable.encode` of its subset, avoiding noncanonical aliases
  admitted by a raw `decode` test. The target build passes.
- Added `Lax842588Proofs.EncodedProjection`: rank-preserving relabeling of trees
  and both directions of the semantic projection theorem, culminating in an
  acceptance iff an accepting source relabeling exists. The target build
  passes.
- Added `Lax842588Proofs.MarkedAlphabetEncoding`: an explicit executable
  `Finset.univ.toList` numbering and rank word for marked symbols, with inverse
  and rank preservation proved. This replaced the earlier noncomputable
  `Fintype.equivFin` choice. The target build passes.
- Exposed `RawFormula.fin?` and `RawFormula.childIndex?` as ordinary concept
  definitions (formerly private) to provide a stable proof API; semantics are
  unchanged.
- The attempted direct syntactic identification with the earlier
  `runSentence` proof was abandoned because its `Fintype.card Q` state-variable
  index is not definitionally the encoded numeric state count. Continue with
  a direct semantic proof for the concrete emitted formula.

At that checkpoint, the next action was to implement the reverse raw-token-to-encoded-automaton
compiler using the encoded operations. Define canonical finite-state
numberings and serializers for the valid-marker and atomic-formula automata,
then recurse over raw formulas using the proved Boolean closure and projection
operations. After effectiveness, instantiate the verified generic IMP+ tree
fold and prove the uniform word-RAM bounds.

### 2026-08-14 continuation

- Repaired and honestly recompiled the complete encoded atomic-automata
  layer. In particular, the child-edge automaton now uses executable finite
  list scans instead of a classical `decide` over dependent existential
  propositions; `edgeCode` is an ordinary computable Lean definition and its
  transition/acceptance correctness proofs compile.
- Completed `EncodedFormulaCompiler.lean`. The reverse compiler handles every
  raw constructor, both marker projections, malformed/ill-scoped formulas,
  and the pullback to the original ranked alphabet. Its uniform language
  preservation theorem compiles end to end.
- Found and fixed a semantic bug in the initial compiler draft: elaboration
  failure must propagate through negation and disjunction, rather than turning
  an ill-scoped negated formula into all valid marked trees.
- Removed unnecessary noncomputability from `bothFO` and `foSO`, and made the
  entire reverse `compileSentence` construction an ordinary executable Lean
  definition.
- Repaired the final dependent-list equality in the forward primitive-
  recursive automaton-to-MSO compiler. `EffectiveTranslations.lean` now
  honestly typechecks.
- Added `UniformEffectiveEquivalence.lean`, combining the two actual uniform
  language-preserving compiler functions. The proof root `Lax842588Proofs.lean`
  typechecks, and a source audit reports no `sorry` or `admit`.

At that checkpoint, remaining theorem work was sharply separated:

1. Prove the intensional mathlib `Computable compileSentence` certificate.
   Executability alone does not discharge this predicate. The clean route is
   a fuel-bounded token parser/compiler carrying an explicit validity bit,
   together with primitive-recursive closure proofs and extensional equality
   to `compileSentence`.
2. Implement and verify the uniform word-RAM program. The pure sparse
   evaluator is already proved correct, but the RAM axioms quantify an actual
   `Lax865980.Ram.Program`; the generic Lax11 tree-fold theorem is non-uniform in
   its table and therefore cannot directly prove the current uniform-input
   statement.

Checkpoint validation: `lake build Lax842588Proofs` passes. There are no
`sorry`/`admit` placeholders in `proofs/Lax842588Proofs`; the remaining unproved
submission claims are the concept axioms for uniform effectiveness and the two
RAM bounds, whose proof theorems have not yet been completed.
Registration remains user-only.

## Current completion checklist

- The revised Lax-58 concept package passes `lax build . --only concepts`.
  Its proof package still describes the previous, larger combinator surface
  and must be adapted after concept review.
- The revised Lax-53 concept root passes `lake build Lax842588` (910 jobs) against
  registered Lax-13 commit `92ae2d6...` and the local Lax-58 override.
- The existing Lax-53 proof package proves the superseded specialized-layout
  runtime statements; it is not evidence for the new distinguished-arena
  statements and is expected to require substantial adaptation.
- A full Lax-53 `lax build` is currently blocked at dependency resolution by
  the installed CLI's demand for an Archive record for Lax-58, even though
  direct Lake builds honor the generated local override.
- The preview remains the last successful pre-refactor Lax build until that
  resolver issue is removed; do not describe it as validating the revision.
- The abstract and equivalence concept attribute the tree result to Thatcher
  and Wright (1968), independently Doner (1970); both full references and DOI
  links were verified in the earlier preview.
- Registration remains user-only.

### 2026-09-03 structural-arena frontend continuation

- The user approved the revised structural-input direction and authorized
  implementation of both Lax-58 and Lax-53. The old “present for review” next
  action is therefore superseded.
- The arena frontend now has checked specifications for opening one
  represented transition, scanning all of its child states, explicitly
  zero-padding its fixed-width row, finalizing that exact row, and advancing
  the certified transition-list cursor.
- A checked counted-loop theorem materializes every transition row. Its
  invariant states pointwise that the consumed prefix equals the corresponding
  `flatMap encodeTransitionFixed` segment, preserves the preexisting table
  header below `records`, and decreases by the remaining transition count.
- `readTransitions_spec` is checked. It initializes and runs that loop, writes
  the reserved transition-count and maximum-rank cells, establishes the exact
  table prefix through the last transition, preserves the certified accepting
  cursor, and carries capacity for the complete evaluator table.
- `readAccepting_spec` is checked. It scans the represented accepting-state
  list with an explicit counted loop, stores each state, fills the reserved
  count cell, and proves that the completed pointwise table is exactly
  `encodeAutomaton (alphabet, body)`.
- `AutomatonRamArenaTreeModel.lean` is checked. It supplies the pure semantic
  model for the iterative DFS: pending postorder output is invariant under
  descent and completion, while its work measure drops by exactly one and is
  initially `2 * treeSize - 1`.
- These results use actual IMP+ `Run`/`Spec` costs. Whole-array equality is not
  treated as a primitive operation; all stores are justified pointwise and
  array-length preservation comes from operational runs.

### 2026-09-04 intrinsic compiler and automaton backend checkpoint

- Completed and checked the distinguished-arena automaton/tree frontend,
  iterative tree traversal, evaluator composition, and transfer to the public
  direct `Lax865980.RamComputes` automaton model-checking theorem. Both the uniform
  automaton-input theorem and its fixed-automaton specialization now have
  compiled proofs.
- Added `IntrinsicFormulaCompiler.lean`. Its compiler recurses directly over
  the intrinsically scoped `Lax146103.MSOSyntax.Formula`; its correctness theorem
  is proved directly by formula induction and the verified primitive
  automata operations.
- Deleted the duplicate `FormulaIR.lean` and `EncodedFormulaCompiler.lean`
  layers. The source tree now contains no `FormulaCode`, `RawFormula`,
  elaboration/reification pass, or encoded-formula compiler. Formula scope and
  constructor shape come solely from the original intrinsic MSO syntax.
- Simplified the value-level automaton-to-MSO direction to the already proved
  intrinsic run sentence. This interface deliberately states only selected
  language-preserving functions, not computability or a runtime guarantee.
- Repaired the node-count normalization proof for automatically derived tree
  presentations after `List.ofFn` reduced to the generic finite-index family.
- Full validation checkpoint: `lake build Lax842588Proofs` succeeds with 3078
  jobs. Focused builds of the intrinsic compiler and value translations also
  succeed. A source audit finds none of the removed formula-code terminology.
- Began the charged uniform-MSO frontend. `MSORamArenaProgram` and
  `MSORamArenaRead` now contain a checked six-read opener for the exact
  `(alphabet, intrinsic sentence, tree)` constructor arena, with certified
  pointers to all three original mathematical values.
- Added the iterative intrinsic-formula traversal and its semantic model. It
  emits subformula occurrences in postorder while carrying their intrinsic
  first- and second-order indices; it introduces no alternate formula syntax.
  The pure model proves preservation of pending output, exact one-step work
  decrease, and a linear bound by the constructor-derived formula structure.
  The four physical traversal stacks now have checked generic push,
  phase-replacement, and pop representation lemmas, and the charged
  initialization of those stacks at the sentence root is verified. The
  charged current-frame loader is also checked: it recovers the certified
  arena root, intrinsic `(n,m)` scope, phase, and original symbolic formula
  constructor name in seven IMP+ assignments.
- Validation after this frontend increment: `lake build Lax842588Proofs` succeeds
  with 3084 jobs.
- All scratch artifacts previously used under `/private/tmp` were copied to
  the workspace-level `tmp/` directory. Future scratch work stays there.

### 2026-09-04 charged intrinsic-formula traversal completion

- Completed the full charged one-step theorem for the intrinsic formula
  phase-stack traversal. The verified `formulaTraversalBody` loads the current
  constructor from the certified arena, emits atomic occurrences, pushes
  unary and quantified bodies with their intrinsic scopes, and handles both
  disjunction-child phases. Every branch increments `formulaSteps` exactly
  once and implements the corresponding `traversalStep` transition.
- Scope bounds for quantified children are derived from membership in the
  original sentence's pending occurrences. They are not extra machine input
  or advice. Stack-space obligations are similarly derived from the exact
  pending-output invariant and the constructor-derived target length.
- Added the counted `formulaTraversalLoop` proof. Its environment-only
  potential `traversalSteps alphabet phi - formulaSteps` is proved equal to
  the pure remaining traversal work and strictly decreases on every actual
  loop execution. On exit, the postorder arrays contain every original
  intrinsic occurrence, `formulaSteps` is exactly the semantic traversal
  count, and the physical stack is empty.
- Added and checked the composed `readFormula_spec`, covering both charged
  initialization and the complete loop while preserving all seven
  preallocated array extents. Focused Lake builds of
  `FormulaArenaTraversalBody`, `FormulaArenaTraversalLoop`, and
  `FormulaArenaTraversalRead` pass (3011, 3012, and 3013 jobs respectively).
- The proof root now imports the complete traversal pipeline. Full validation
  after the import and warning cleanup: `lake build Lax842588Proofs` succeeds with
  3092 jobs.

### 2026-09-04 charged compiler storage foundation

- Added the pure postorder compiler transition model and proved that folding it
  over the certified occurrence stream yields the same numeric automaton as
  direct recursion on the original intrinsic formula.
- Added proof-private append-only transition and accepting heaps plus a
  five-word descriptor stack.  Physical descriptors are stored bottom-to-top
  and are proved to represent the reverse of the pure head-as-top compiler
  stack.
- Strengthened the stack invariant with an explicit separation certificate:
  every immutable transition and accepting segment ends no later than its
  live heap cursor.  This is the fact needed to compile a right subformula
  without overwriting a left-subformula automaton still on the stack.
- Added charged descriptor preparation and push specifications.  The falsum
  case now constructs and pushes the semantic one-state empty automaton inside
  the IMP+ execution, with no table copying.
- Added charged one-word append commands for both compiler heaps.  Their
  checked specifications grow the exact pointwise heap prefix and preserve
  every previously stacked automaton using the cursor-separation invariant.
  Focused Lean checks of `MSORamCompilerHeap` and the strengthened empty case
  pass.
- Added and checked a counted fixed-width transition-record writer.  It
  appends the three semantic header words and exactly `maximumRank` prepared
  child cells, preserves all older stack descriptors, and is related directly
  to the existing proof-private `encodeTransitionFixed` function.  Its actual
  IMP+ cost is bounded by `100 + (64 * maximumRank + 4)`.
- Added charged top-descriptor loading and logical pop.  The storage proof
  derives the top descriptor from `List.Forall₂.get`, derives the tail stack
  with `List.Forall₂.take`, and leaves both immutable heaps untouched.
- Added the generic automaton-build boundary.  A charged opener records the
  live heap cursors, and a checked finalizer turns exact transition/accepting
  suffixes into `StoresAutomaton` before invoking the charged descriptor push.
  Operation-specific automaton constructors therefore need only prove the
  suffixes that they actually generate.
- Added the first advice-free numeric row generator for a nonempty primitive
  automaton.  `binaryWord` is proved exactly equal to the canonical
  `FiniteAutomatonEncoding.words 2` enumeration, and the alternative
  `binarySomewhereCode` lists one semantically correct transition per child
  row in the order a simple RAM loop can emit.  The fixed IMP+ decoder writes
  a row by successive quotient/remainder steps; its counted-loop invariant
  proves the written prefix plus unread recursive suffix is always the exact
  canonical row.  Its charged bound is `104 * rank + 44`, and neither the
  complete word list nor any advice array is runtime input.
- Completed the fixed-width continuation of that generator.  A second counted
  loop zero-pads from the actual symbol rank through `maximumRank`, after
  which the entire `NewTransitionChildren` array is proved equal to the
  existing `preparedChildren` value for the transition.  The combined charged
  bound is `104 * rank + 34 * maximumRank + 48`.  A `Spec.frame` corollary now
  proves this preparation preserves the logical compiler stack and both exact
  heap prefixes.  `CompilerStorageAgrees` isolates the small reusable storage
  footprint needed for such framed arithmetic phases.
- Composed the padded row generator with the checked transition-record writer.
  The resulting theorem appends exactly the semantic fixed-width record,
  preserves both immutable compiler heaps and all prior descriptors, and
  retains the exact generated child buffer.  A counted wrapper advances
  `newTransitionCount` only after that record has been written.
- Proved that a canonical binary row contains a `1` exactly when its numeric
  row index is nonzero.  The charged header therefore computes the two-state
  automaton's parent using one zero test, while remaining definitionally tied
  to the mathematical `children.any` transition condition.
- Completed and checked the full counted inner row loop for one symbol.  Its
  invariant tracks the precise `flatMap encodeTransitionFixed` heap prefix,
  descriptor count, compiler stack, accepting heap, fixed symbol/rank data,
  and capacity reserved for all `2 ^ rank` rows.  No exponential word list is
  materialized.  The focused build passes through 3022 jobs.
- Added the proof-private outer structural-alphabet compiler for equality
  atoms. It decodes every packed marked symbol back to its base-alphabet rank,
  extracts the two first-order marker bits arithmetically, traverses every
  binary child-state row, and proves that the final fixed-width heap suffix is
  exactly `transitionWords` for the sparse two-state somewhere automaton.
  The outer counter and transition count are related to explicit semantic
  prefix functions; no rank list, marker-bit vector, word enumeration, or
  transition table is supplied as input.
- Completed the equality atom end to end inside IMP+: charged instructions
  open a fresh two-state segment, initialize its bases and counters, execute
  the complete marked-alphabet traversal, append accepting state `1`, set the
  accepting count, and push the five-word descriptor. The checked
  postcondition is `CompilerStackRep` with the pure equality automaton at the
  logical top. The focused `MSORamCompilerSomewhere` build succeeds through
  3032 jobs. Full proof-root validation after this end-to-end constructor
  succeeds through 3104 jobs (`lake build Lax842588Proofs`).
- Verified the two remaining somewhere-atom predicate fragments. The label
  fragment combines the decoded base-symbol comparison with one first-order
  marker bit; the membership fragment combines a first-order and a
  second-order marker bit. Both operate arithmetically on the packed symbol,
  export the same framed predicate contract as equality, and pass the focused
  3032-job build.
- Factored the complete two-state atomic-automaton lifecycle over that framed
  predicate contract.  The common checked pipeline now owns symbol-rank
  decoding, row generation, heap/counter evolution, descriptor opening,
  accepting-state finalization, and descriptor push; concrete atoms supply
  only their operand context, predicate preparation, and syntactic non-write
  certificates.
- Instantiated the shared outer loop and full charged lifecycle for label and
  membership atoms.  `compileLabelAtomicAutomaton` and
  `compileMembershipAtomicAutomaton` now construct their exact sparse
  two-state codes and leave those codes at the logical top of
  `CompilerStackRep`, just as the equality constructor does.  A direct Lean
  check of the complete `MSORamCompilerSomewhere` module passes.
- Proved that the sparse row-generated `binarySomewhereCode` has exactly the
  same automaton semantics as the earlier complete-enumerator
  `somewhereCodeP`.  The pure postorder target is now
  `compileFormulaForRAM`: it uses the sparse code for equality, label, and
  membership while retaining the already proved numeric closures.  Its
  formula-induction correctness theorem and exact postorder-fold theorem both
  compile, so the operational row order is no longer required to equal the
  older transition-list order.
- Removed an unused import from compiler storage to restore the intended
  dependency direction: the pure postorder model may depend on sparse
  automata, while storage remains independent of the formula compiler.
  Former transitive consumers now import marked-alphabet/intrinsic-compiler
  definitions directly.  Full proof-root validation after this cleanup and
  the sparse semantic bridge passes all 3104 jobs.
- Added the reusable proof-only `spec_arrayLength_eq` rule: every IMP+ command
  preserves every array extent even when it stores into that array.  This is
  operational bookkeeping, not a new concept-level representation contract.
- Full proof-root validation after the inner-loop checkpoint succeeds through
  all 3103 jobs (`lake build Lax842588Proofs`).
- Full integration validation before the binary-row addition passed through
  all 3102 jobs.  The focused Lake build of
  `MSORamCompilerBinaryWord` then passed through 3019 jobs; the proof root
  imports the new module.

### 2026-09-04 generic radix row-generation foundation

- Added `FiniteAutomatonEncoding.radixWord` and proved that it agrees exactly
  with the canonical `words base length` row at every in-range numeric index.
  The proof also establishes fixed length, membership in the canonical word
  enumeration, and the bound on every decoded digit.
- Added a generic arbitrary-radix IMP+ decoder. Its initial divisor
  `base ^ (length - 1)` is computed by a charged multiplication loop; neither
  exponentiation nor a precomputed power/word table is treated as a machine
  primitive or runtime advice.
- Proved the decoder's exact-prefix quotient/remainder invariant, linear
  instruction bound, maximum-rank zero-padding theorem, and compiler frame
  theorem preserving the descriptor stack and both immutable heaps.
- Composed generic radix materialization with the existing fixed-width
  transition writer. Constructor-specific code now only has to prepare a
  checked parent-state register; the shared theorem appends the exact semantic
  transition record for the indexed child row.
- Added a pure sparse deterministic-automaton presentation and proved it has
  exactly the same automaton semantics as the complete parent-enumerating
  encoder whenever the transition relation tests the uniquely computed
  parent. This is the semantic target for advice-free valid, edge, and other
  deterministic row generators.
- Added mutually inverse arithmetic conversions between bounded radix words
  and their numeric values.  The valid-marking automaton's unique parent is
  now the base-3 value of its forced occurrence-count digits.
- Added `sparseValidCodeP`, proved its decoded automaton equal to the original
  complete-enumerator `validCodeP`, and changed `compileFormulaForRAM` plus
  its postorder step model to use the sparse code.  The full formula-language
  correctness theorem still holds, while the operational target now has one
  transition per child row rather than testing every possible parent.
- Focused checks of `FiniteAutomatonEncoding`,
  `MSORamCompilerRadixWord`, `SparseDeterministicAutomaton`,
  `SparsePrimitiveAtomicAutomata`, and the revised intrinsic postorder
  compiler pass. A full proof-root build passed all 3106 jobs before the
  sparse-valid target substitution; its focused downstream build then passed
  all 3024 jobs. Scratch work remains under the workspace-level `tmp/`
  directory.

### 2026-09-04 specification reread

- Read `FORMALIZATION_STATE.md` in full, then read the current output of
  `lax print instructions` and the complete 1,326-line Lax specification
  printed by `lax print spec`. Because the first specification rendering was
  truncated, repeated the read with the non-overlapping ranges `1,350`,
  `351,700`, `701,1050`, and `1051,1400` via `sed -n`.
- No build or validation was run and no formalization source was changed. The
  specification confirms the existing invariants about concept/proof
  separation, generated files, pinned dependencies, root modules, axiom
  hygiene, full-build milestones, and user-only registration.
- No blocker or next action changed at this read-only checkpoint.

### 2026-09-04 closed certified field derivation

- Replaced the temporary `structuralLaw%` client with four
  `derive_certified_encoding` invocations for terms, relations, formulas, and
  ranked trees. Each creates its encoder, complete `.Laws`, and checked
  `.certified` witness in the client namespace.
- The new Lax-58 `CertifiedDerivation` module uses a private witness constructor
  and private registry. Field resolution accepts only Nat, Fin, proof-erased
  subtypes, finite families, and previously generated datatype witnesses;
  ordinary `FieldEncoding` instances are never consulted. Unsupported
  implicit fields and implicit payloads that are not indices are rejected.
- The generator embeds checked witness expressions directly, without a
  pretty-printer/re-elaboration round trip. Failed commands roll back their
  generated declarations and do not register a partial certificate.
- Updated the structural-law proofs to project the generated witnesses and
  adjusted the injectivity/arena-size proofs to use certified primitive
  fields. Representation equations preserve the previous raw layout.
- Both regression suites pass (`lake env lean ../tests/CertifiedDerivation.lean`
  from Lax-58 concepts and `lake env lean ../tests/CertifiedRepresentations.lean`
  from Lax-53 concepts). They cover transitive fields, dependent families,
  malicious low-level instances, unsupported and hidden fields, rollback,
  private-constructor/record-update rejection, concrete client equations, and
  axiom audits. Client witnesses depend only on the three allowed background
  axioms, not on the public structural-law axioms.
- The focused Lax-53 concept build and revised structural proof module pass.
  Lax-58 full validation with independent kernel replay passes all five
  concepts and fifteen proofs. Full Lax-53 integration is in progress.
- Retried `lax build . --only concepts --no-color`. Layout passes after moving
  the two package `.DS_Store` files to the recoverable backup directory
  `/private/tmp/lax53-layout.gqgzSe/`. Archive resolution remains blocked by
  missing content-bearing Lax-58/Lax560851Proofs records and a Lax62Proofs source-pin
  mismatch. No dependency pins, commits, or publication state were changed.

### 2026-09-05 certificate audit correction

- A constructor-tactic probe showed that a private record constructor is not
  a kernel seal. The original registry-based derivation did not accept the
  fabricated record, but the stronger claim about standalone witness values
  was incorrect.
- Strengthened `CertifiedFieldEncoding` with type indices for its canonical
  function and generated law, plus a proof that its stored function equals
  the canonical one. The command remains the provenance boundary and never
  accepts arbitrary standalone certificate values. Lax-53's four compact
  invocations are unchanged and its concept module compiles.
- The new regression suite defeats the constructor-tactic constant-42 attack.
  Interrupted the older full build at 3075/3109 jobs and restarted validation
  of the strengthened design with `LEAN_NUM_THREADS=2`.

## 2026-09-05 workflow and current-state handoff

- Split concise `CURRENT_STATE.md` from this preserved historical log;
  `FORMALIZATION_STATE.md` now redirects to the new documents. Updated agent
  instructions and the cross-repository boundary handoff.
- Added `WORKFLOW.md`: operation completion requires a pure specification,
  concrete program, bounds, exact storage/output representation, lifecycle
  instruction cost, actual compiler-step composition, and validation evidence.
  It reuses the existing storage contracts instead of adding another framework.
- Distinguished charged somewhere components from complete atomic formula
  steps. The next implementation milestone is sparse-valid construction,
  followed by charged intersection. The headline runtime theorems remain open.
- Added focused validation scripts (both repositories pass), and an expanded
  certificate report with recursive defining equations, all four generated
  law groups, witness definitions, and axiom dependencies. The `--proofs`
  option also exposes extracted reduction-proof helpers. Both display modes
  pass; default output includes all four axiom reports without proof bodies,
  and proof-expanded output includes the generated reduction-proof bodies.
- Shell syntax and whitespace checks pass. The latest full Lax-53 proof-root
  rebuild is still running; do not infer a completed full build from the
  successful focused checks. Archive blockers and pins are unchanged.

## Exact next action at the preceding encoding checkpoint

Implement the remaining numeric primitive automata and closure operations
used by the intrinsic postorder compiler, accounting for all construction
cost in the same RAM run. Finally compose that compiler with the completed
automaton/tree RAM backend to prove the headline intrinsic-sentence theorem
and derive the genuine fixed-sentence tree-only companion. Do not discharge
the headline theorem by performing the pure Lean compilation outside the
measured RAM run.

## 2026-09-05 separate Lax-58 definitions from derivation tooling

- Changed the structural-representation import to
  `Lax560851.CertifiedDerivationElab`. The four command invocations, semantic
  encoding layouts, and public law obligations are unchanged.
- The shared agreement record stays in the small `CertifiedDerivation`
  module; the command and closed registry are separately labeled tooling.
- Updated the certificate report to print the checked packaging function
  and discover extracted proof helpers by namespace, instead of assuming
  exactly two numbered helpers per witness. Both report modes pass; default
  output retains all four axiom reports without the extracted proof bodies.
- Focused validation passes: 900 concept build jobs, the concrete encoding
  tests and four axiom guards, and 904 structural proof build jobs.
  Lax-58's full six-module / fifteen-proof replay passes.
- Stopped the prior full root build at 3090/3109 before rebuilding shared
  dependencies, then started a fresh two-thread full proof-root build after
  focused validation. Its result is pending in `CURRENT_STATE.md`.
- No compiler semantics, archive dependency pins, or publication state changed.

## 2026-09-05 generic primitive-recursive execution bridge — foundations

- User accepted replacing the operation-by-operation charged compiler proof
  strategy with a reusable execution bridge. Freeze Lax-58 and the Lax-53
  concepts. Keep all compilation in the measured uniform RAM run; exploit
  only the theorem's permission for an arbitrary computable parameter
  coefficient. Preserve existing bespoke implementations during validation.
- Fixed and built `PrimitiveRecursiveCode`: exact seven-case `Nat.Primrec`
  code semantics and the typed decoding/`Option` output convention. Its
  existential code theorem is not itself machine realization.
- Added bounded pairing/unpairing in `PrimitiveRecursivePairing`. The square
  root is computed by subtracting consecutive odd numbers. Its invariant is
  `n = s*s + r`, its decreasing variant is the remainder, and the loop has
  a concrete instruction bound. Pairing and both projections use only
  ordinary IMP+ arithmetic/loops; scratch names are parameters.
- Added `PrimitiveRecursiveCompile`: finite command generation for all seven
  constructors, an injective register naming convention, lower-register
  preservation, no array writes, no input reads, and no output writes.
- Added `PrimitiveRecursiveBounds`: primitive-recursive envelopes uniformly
  over inputs up to `N`, a monotone iterative ceiling for recursion, and
  proofs bounding inputs and pure results. An envelope alone is not the
  machine cost proof.
- Added `PrimitiveRecursiveCorrectness`: bounded execution for the four base
  cases, composition, and pairing. The primitive-recursion execution case is
  still missing; no general realization theorem or completed intersection
  RAM program is claimed. All five modules are imported by the proof root.
- Full local integration passed first at 3110 jobs (pre-bridge), then at
  3115 jobs (including the new modules). Focused correctness build passed
  at 2988 jobs. Axiom reports for the implemented bridge lemmas contain only
  allowed background axioms; guarded regression tests are in
  `tests/PrimitiveRecursiveBridge.lean`, run by
  `bash scripts/check-primitive-recursive.sh`.
- That focused script passed after correcting the test's automaton-type
  namespace: semantic examples, bounded zero-input/aliased-output examples,
  intersection source-code existence, and seven explicit axiom guards.
- Full `lax build . --replay --no-color` still fails at archive resolution:
  missing content-bearing Lax560851/Lax560851Proofs records and the unchanged
  Lax62Proofs pin mismatch. No pins, commits, or publication state changed.
- Next proof: use `recCeiling` as the accumulator bound for the primitive
  recursion loop, preserve parameter/bound/counter/accumulator registers
  across the step call using `compile_frame`, and discharge the coarse
  instruction allowance `200 * (N + 1) * (recCeiling ... N N + 1)`.
  Then close structural compiler correctness, transfer through the existing
  IMP+-to-RAM simulation, and apply the complete bridge to `inter_prim`.
  Runtime arena conversion, full compiler materialization, computable
  parameter-only bounds, and both headline proofs remain after that.

## 2026-09-05 generic bridge closed and applied to RAM intersection

- Added `PrimitiveRecursiveRecursion.lean`. The recursion step explicitly
  composes two pairing programs, the recursively compiled step, accumulator
  copying, and counter increment. Its invariant preserves the parameter and
  bound and controls the accumulator by `recCeiling`. Initialization and
  the counted loop close `PrimitiveRecursiveCorrectness.compile_correct`
  for all seven constructors, with bounded IMP+ execution and instruction
  cost. No execution axiom or uncharged evaluator call is used.
- Added `PrimitiveRecursiveLayout.lean`: input-independent scalar layout,
  expression temporary capacity, and `Com.Ok` for every generated program.
- Added `PrimitiveRecursiveRam.lean`: read/compute/write wrapper,
  `runner_solves`, actual `code_computes`, and generic `exists_ram` /
  `exists_typed_ram` theorems via Lax-13's verified simulation. The resources
  are primitive recursive; word fit includes layout addresses as well as
  intermediate values. The typed output retains its `Option` encoding tag.
- Added `PrimitiveRecursiveAutomata.inter_ram`: one fixed RAM program
  computes the existing numeric intersection function with computable
  resources. This validates the requested first-operation milestone. Its
  one-word representation is an internal interface, not a new public input
  convention; constructing/decoding it from the certified arena remains
  charged implementation work.
- Focused operation build passes at 2997 jobs. Full proof-root integration
  passes at 3119 jobs. Explicit `leanchecker -v` replay passes for all nine
  `PrimitiveRecursive*` proof modules. The generic compiler, typed RAM
  theorem, and intersection theorem report only `propext`,
  `Classical.choice`, and `Quot.sound` in their axiom sets.
- Expanded the regression file to include a real RAM zero-iteration case,
  a positive recursion/addition case, and ten explicit axiom guards. The
  positive example uses a separately proved concrete evaluation equality;
  kernel definitional equality alone did not normalize its paired input.
- The expanded regression file passes, including both actual RAM examples
  and all ten explicit axiom guards. Root import inventory and whitespace
  checks pass. No verification process from the prior checkpoint remains
  unaccounted for; full integration and explicit bridge replay completed.
  The complete focused script was rerun after the final test correction and
  exited successfully (2997 build jobs plus the expanded test file).
- Source review for the next phase: existing formula traversal emits
  `FormulaOrder`, `FormulaFOOrder`, and `FormulaSOOrder`; its occurrence
  loader and original intrinsic compiler are already verified. Original
  `validCodeP`, `somewhereCodeP`, and `edgeCodeP` have primitive-recursiveness
  proofs, unlike the sparse variants. Prefer the existing original pure
  compiler for the generic fold to avoid rebuilding sparse optimizations.
  Internal normalized field data must omit global arena addresses and tree
  data so the compiler envelope depends only on the mathematical parameter.
- No concepts, certified encoding layouts, dependency pins, or publication
  state were changed. The full uniform compiler and both headline proofs
  remain the active goal, not completed by this internal-interface result.

## 2026-09-05 — full internal compiler and charged packing

- Rechecked the worktree and durable handoff after the user's simplification
  question. The previous turn was explanation-only; implementation resumed
  without changing the objective, public concepts, certified input, or pins.
- Finished `IntrinsicCompilerComputability.compileRows_prim` by specifying
  the product domain at the fold's stack-step application. The full
  `IntrinsicCompilerRam` target builds (3022 jobs). The exact stack-fold
  theorem covers all intrinsic constructors and preserves arbitrary prior
  stack contents; there is no second public formula datatype.
- Added `IntrinsicCompilerOutput`: primitive-recursive formatting into the
  existing evaluator table is inside the charged generic compiler call.
  `compileTable_eq` identifies the table exactly. This removes the need for
  a separate RAM implementation of nested automaton-record formatting.
- Added `CompilerArrayPacking`: a counted backward scan encodes an array
  prefix using actual pairing arithmetic. Its `program_spec` has a
  `60 * (xs.length + 1)` IMP instruction bound and explicit arithmetic
  word-fit precondition. No source-array padding is read; all arrays and
  both tapes are preserved. A syntax/layout lemma supports later lowering.
- Added `tests/IntrinsicCompilerBridge.lean` and
  `scripts/check-intrinsic-compiler.sh`. The focused script passes: 3025
  build jobs, constructor/stack/flat-output examples, empty and nonempty
  packing specifications, and five axiom guards with background axioms only.
- Root module imports all five new proof modules; exact import inventory
  and whitespace checks pass. Full root build passes after the final layout
  lemma (3124 jobs). Explicit `leanchecker -v` replay passes for all five new
  modules: `IntrinsicCompilerFields`, `IntrinsicCompilerComputability`,
  `IntrinsicCompilerRam`, `IntrinsicCompilerOutput`, and `CompilerArrayPacking`.
  The full Lax retry passes layout but encounters the same three archive
  dependency errors; no concept/pin/publication change.
- Remaining end-to-end obligations: runtime construction of normalized
  fields from the certified arena, packing/composing the generic subroutine,
  counted flat-list output unpacking, evaluator initialization, computable
  parameter-only envelopes, and both unchanged headline runtime proofs.

## 2026-09-05 — materializing compiler body and shared field reads

- The previous goal turn was concrete progress: complete internal compiler,
  flat-table formatter, and counted input packing, all built/replayed. Read
  the authoritative handoff and worktree again before proceeding.
- Added `CompilerArrayUnpacking`. `splitCell_spec` reuses the counted
  square-root/unpairing routines. A forward loop tracks an exact written
  prefix and encoded remaining suffix, preserving array extents. Its bound
  is `170 * (encode xs + 1) * (xs.length + 1)` IMP steps under
  `2 * encode xs + 3 < B`, with explicit array capacity. No tape I/O occurs.
- Added `IntrinsicCompilerMaterialize`: compose the actual generic IMP
  compiler body, strip the output `some` tag, and unpack into the evaluator's
  `P` array. `materialize_exact_spec` proves exact table equality;
  `exists_tableCompiler` instantiates it for the complete intrinsic compiler.
  Resource envelopes `300 * (budget c n + 1)^2` and `3 * budget c n + 10`
  are primitive recursive in the internal input. Array-layout address bounds
  remain part of eventual whole-program lowering, not silently included here.
- Added `ArenaFieldAccess`: fixed binary paths select existing constructor
  fields; correctness follows the represented raw value through ordinary
  bounded word reads. Assignment cost is `3 * path.length + 5`, and a layout
  lemma accounts for expression temporaries. This avoids duplicating pointer
  access arguments in every intrinsic formula constructor case.
- Extended the focused regression script and file. The script passes at
  3041 build jobs, including empty/nonempty materialization and eight axiom
  guards (background axioms only). One guard needed the actual multiline
  diagnostic formatting; no axiom expectation was weakened.
- Root import inventory and whitespace checks pass. Full root build passes
  (3127 jobs); explicit `leanchecker -v` replay passes for all three new modules.
  A source scan finds no `sorry`, `admit`, or new axiom in these modules. The full
  Lax retry still passes layout and fails at the same three archive dependency
  checks. No concepts, certified layouts, dependency pins, commits, or
  publication state changed.
- Next: implement normalized-field extraction over the existing postorder
  occurrences using the shared field-reader lemma, pack the internal input,
  and connect to the materializing body. Parameter-only bounds, evaluator
  initialization/composition, and both headline theorems remain unfinished.
- Source-inspected candidate paths for that next extractor (not yet Lean
  instantiated against every constructor): equal's term variables use
  `[true,false,true,false]` and `[true,true,false,true,false]`; a relation's
  primitive symbol/child value uses the first path, and its constructor tag
  uses `[true,false,false]`; relation-term variables use
  `[true,true,false,false,true,false]` and
  `[true,true,false,true,false,true,false]`; membership's set index uses
  `[true,true,false]`. Scope counts come from the verified occurrence arrays.
  Use fixed runtime constructor dispatch, not a program chosen from the input
  formula. `MarkedTrees.treeTerm_eq_var` can expose variable terms by an
  explicit rewrite; broad simplification with it can loop.

## 2026-09-05 — certified occurrence field extraction and row packing

- The preceding explanation-only goal turn was no implementation progress.
  Revalidated the worktree and polled the existing field-extraction build
  handle, which had terminated with proof errors; continued from those errors.
- `IntrinsicFieldPaths` checks the generated layouts for equality, membership,
  label, and child fields. The tag-injectivity lemma uses the proved Lax-58
  constructor theorem, not the concept axiom.
- Completed `IntrinsicFieldExtraction.program_spec`: one fixed program uses
  runtime tags to dispatch across every intrinsic formula constructor and
  writes all six normalized fields. The bound is 500 IMP steps. Proved array
  and tape preservation and the finite-register layout (nine temporaries).
  The VCG does not prune unreachable branches, so the proof identifies the
  selected branch before applying its field-reader specifications.
- Added fixed-register packing to `CompilerArrayPacking`, reusing charged
  pairing. Its bound is `25 * (register count + 1)`, with explicit word bounds
  and a non-aliasing premise. No temporary row array is required.
- The composed `IntrinsicFieldExtraction.packedProgram_spec` builds with
  bound 675, preservation facts, and a layout lemma. The latest build reports
  this module successful after correcting the layout-proof syntax.
- Added `IntrinsicOccurrenceInput` to compose the existing postorder loader
  with extraction/packing (target bound 825 and preserved advanced index).
  Its first build (`53134`, now terminal) failed on unresolved implicit
  register arguments in the preservation lemma. Supplied those arguments
  and started the focused regression script in session `42927`; poll that
  handle rather than restarting. Root imports and regression cases/axiom
  guards are added. Full root build and replay remain to run.
- No concepts, certified layouts, pins, commits or publication state changed.
  Full postorder input assembly, evaluator composition, parameter-only bounds,
  and both headline runtime theorems remain unfinished. The goal stays active.

## 2026-09-05 — whole-formula input and measured compiler composition

- Previous goal turn was progress: all-constructor extraction, register row
  packing, and a first occurrence-loader composition. Polled its specific
  live regression handle; it passed (3052 jobs, twelve axiom guards).
  Explicit kernel replay then passed for the changed packer and three
  field/occurrence modules.
- Added `IntrinsicFormulaInput`. A fixed backward scan uses the existing
  occurrence loader, extracts all six fields, packs the row, and prepends it
  through charged pairing. No extra row array is used. Its invariant tracks
  the encoded remaining postorder suffix; `encode_rowCodes` identifies the
  result with the exact list-of-rows compiler convention. The full bound is
  `1000 * (occurrence count + 1)`. Context construction from `FormulaOrderRep`,
  capacity and scope facts is proved, as are preservation and fixed layout.
- Added `IntrinsicAlphabetInput`: scan the already decoded `P` prefix
  including its length header, then remove the header by the proved counted
  unpairing routine. Reuses existing packer and reader with no rank copy.
  Exact alphabet result, array/tape preservation, and layout are proved.
- Added `IntrinsicCompilerFromArena`: one counted body starts from those
  prepared working arrays, constructs both numeric inputs, executes the
  complete intrinsic compiler and materializes its exact evaluator table.
  `exists_compiler` builds with explicit word/capacity bounds, no tape I/O,
  writes confined to `P`, and a compositional `Com.Ok` proof. The compiler
  code is chosen once for all inputs, not separately for an input formula.
- The combined result does not yet start at the public input tape or emit a
  model-checking answer. Its `Ready` context must be connected to the public
  arena reader/opener/alphabet reader/formula traversal. The existing tree
  reader and evaluator must be composed, and resource premises must follow
  from computable parameter-only coefficients.
- `bash scripts/check-intrinsic-compiler.sh` passes: 3058 build jobs and
  fifteen axiom guards, all background-only. Includes actual field-path
  checks, row-encoding compatibility, and empty-alphabet header stripping.
  One earlier script run failed because its source was extended while Bash
  was still reading it; current source is correct and the fresh run passed.
  Do not edit running shell scripts.
- `env LEAN_NUM_THREADS=2 lake build Lax842588Proofs` passes (3134 jobs).
  Explicit `leanchecker -v` replay passes for `IntrinsicFormulaInput`,
  `IntrinsicAlphabetInput`, and `IntrinsicCompilerFromArena`. Root inventory,
  whitespace check, and no-sorry/admit/axiom source scan pass.
- Full `lax build . --replay --no-color` retry passes layout and encounters
  the same three archive-resolution errors: missing Lax560851/Lax560851Proofs record
  content and the Lax62Proofs source mismatch. No pins, concepts, certified
  layouts, commits or publication state changed. All launched checks are
  terminal; the thread goal remains active.
- Exact next integration: use `IntrinsicFormulaInput.context_of_order` and
  `IntrinsicAlphabetInput.prefix_of_alphabetRead` to establish `Ready` after
  the public frontend; then initialize `EvalFields` from `P`, read the tree,
  and apply `automatonBackend_spec`. Preserve zero workspace arrays through
  the compiler via its frame theorem. Both headline theorems remain open.

## 2026-09-05 — public-input model checker reaches the actual RAM

- Progress classification: concrete implementation and validation progress;
  the full thread goal remains active. No publication or pin authority was
  inferred from the ongoing implementation request.
- Completed `IntrinsicCompilerPrepare` and strengthened `IntrinsicPublicCompiler`:
  public arena reading, opening, alphabet decoding, formula traversal,
  runtime field extraction/packing, full compilation, and exact table
  materialization are one counted computation. The postcondition retains the
  represented input tree and arena, using `IntrinsicCompilerFrame`.
- Fixed the evaluator-header elaboration timeout with a local heartbeat
  allowance. `IntrinsicEvaluatorPrepare` now combines the existing generic
  tree reader with this header, without another input read or a supplied
  automaton table.
- Added `IntrinsicSentenceCorrectness`: zero-marker symbol codes are the
  original alphabet numbers, so the unmodified normalized compiler's output
  decides the original sentence. No additional runtime pullback is necessary.
- Added `ImpLayout`: extending layouts preserves expression/command validity,
  and every finite IMP command has an input-independent finite layout.
- Added `IntrinsicModelChecking` and `IntrinsicModelCheckingRam`. The former
  composes the full IMP execution and proves initialization from zero arrays;
  the latter chooses compiler/layout once and applies the instruction-level
  simulation to the unchanged public tape, obtaining `ComputesInTime` for
  the original sentence-satisfaction output. It retains explicit resource
  premises and therefore is not either headline complexity theorem.
- Added `IntrinsicParameterFields`: occurrence scope and extracted field
  bounds in mathematical sentence/alphabet/rank sizes. Next bound the internal
  input number and use computable finite-prefix resource maxima. No monotonicity
  theorem for `budget c` has been proved; do not silently assume one.
- Public trust audits found two inherited concept-axiom references. Replaced
  `encodeRaw_represents` in `MSORamArenaRead` and `Raw.constructor_eq_iff` in
  `FormulaArenaTraversalBody` with existing Lax-58 proof counterparts. The
  rebuilt public RAM theorem and all ten directly audited interfaces report
  only the three allowed background axioms.
- Public RAM target passes (3113 jobs); full proof-root build passes (3144
  jobs). All ten new modules are imported directly by the proof root. Root
  inventory, whitespace, and no-sorry/admit/axiom-declaration source scans pass.
- Focused regression script session `88428` passed (3114 build jobs, both test
  files, and 26 background-only axiom guards). Tests include the public-input
  path, eleven new guards, header no-read checks, generic layout existence,
  and zero-scope symbol numbering. Kernel replay session `23862` passed for
  all ten new modules and the two changed upstream modules. Full-root session
  `88638` passed as well. Every launched check is terminal; none remains running.
- Full Lax validation again passes layout and stops at the unchanged three
  Lax560851/Lax560851Proofs content-record and Lax62Proofs pin-resolution errors.
  Local overrides and public concepts remain unchanged; no commit or external
  mutation was performed.

## 2026-09-05 — Parameter-bound progress and status check

- Added numeric list bounds and computable finite-prefix maxima in
  `CompilerNumericBounds`; focused build passed.
- `IntrinsicParameterEncoding` bounds the internal alphabet/formula encoding
  by `parameterSize`; `IntrinsicCompiledTableBounds` supplies a parameter-only
  bound on table entries and dimensions. Both focused builds passed.
- Polled existing build session `59527` during the status check. It terminated
  with `IntrinsicCompilerParameters` passing and `IntrinsicInputBounds` failing
  on four unresolved `treeSize` references. No build remains running.
- These five new modules still need root integration, focused regressions,
  axiom audits, and kernel replay. Earlier full-root validation does not cover
  this new layer. Both headline theorems remain unfinished.
- Next: fix the input-bounds name resolution, then assemble time/word
  coefficients and discharge the public RAM theorem's explicit premises.
  No proof source, dependency pin, or external state was changed by this
  status check; refreshed the current-state handoff and this history.

## 2026-09-05 — Both unchanged MSO headline proofs implemented

- Fixed `IntrinsicInputBounds` by opening only `treeSize`, avoiding the
  legacy automaton-input namespace's ambiguous size definitions.
- Added `IntrinsicTimeBounds`: charged public input reading, alphabet/formula
  packing, complete compilation/materialization, tree preparation, and
  evaluator execution are bounded by a primitive-recursive parameter-only
  coefficient times `treeSize + 1`.
- Added `IntrinsicWordBounds`: one primitive-recursive coefficient covers
  compiler premises, table dimensions/values, arena values, tree workspaces,
  and the chosen finite RAM layout's address span.
- Added the annotated uniform headline proof in
  `IntrinsicUniformModelChecking`. Its type is the original concept statement;
  neither the program's quantifier order nor the certified public input was
  weakened. Formula compilation remains part of the measured RAM run.
- Added `FixedTableLoader`, `FixedSentencePrepare`, and
  `FixedAutomatonModelChecking`. For a fixed sentence, the program contains
  its fixed automaton, initializes the table using the verified decoder during
  counted execution, and receives only the certified tree arena. Initial
  machine memory remains zero; no supplied compiled table is assumed.
- Added `FixedSentenceModelChecking`, including the annotated original
  fixed-sentence headline. Its linear time and word bounds include table
  initialization, tree reading, evaluator work, and finite-layout addresses.
- Integrated all twelve new numeric/parameter/headline/fixed-sentence modules
  directly into the proof root. Full build passes: session `12059`,
  `env LEAN_NUM_THREADS=2 lake build Lax842588Proofs`, 3156 jobs.
- Extended `scripts/check-intrinsic-compiler.sh` with two new test files.
  Session `23121` passes (3129 build jobs, four test files): both headline
  types are definitionally equal to their unchanged concept statement types,
  and all 38 axiom guards report only `propext`, `Classical.choice`, and
  `Quot.sound`. Corrected expected line wrapping in the long headline guards;
  the first uniform audit already had the correct axiom set.
- Both closed-certification suites pass again, session `7534` (437, 900,
  and 904 build jobs). No shared encoding API or concept was changed.
- Root inventory, whitespace, and no-sorry/admit/axiom source checks pass.
- Independent replay of all twelve new modules passed in session `24524`
  with `LEAN_NUM_THREADS=2`. It printed every target and exited zero. All
  implementation and validation sessions are now terminal.
- A diagnostic `leanchecker --help` unexpectedly started whole-project replay:
  this tool ignores unknown flags and defaults to the package root. Stopped
  that diagnostic process with approved SIGTERM; session `39496` is terminal
  exit 143. The explicit targeted replay is a different, uninterrupted run.
- Full Lax retry passes layout and stops at the unchanged three dependency
  resolution errors. No pins, commits, publication, or registration changed.
  Archive reconciliation remains a separate authorization gate, not a missing
  compiler or headline proof. Updated `CURRENT_STATE.md` and `WORKFLOW.md`.

## 2026-09-05 — Requested Lax842588 submission: dependency compatibility gate

- User requested that Lax842588 also be submitted. Lax560851's submission has now
  succeeded at source `szymtor/lax58@53278a48b0605bde8cfc9510066ee797d085a6f1`.
  Updated Lax842588's Lax560851/Lax560851Proofs requirements to this exact accepted source.
- Refreshed Archive records and provisionally pinned Lax62Proofs to current
  `4001304840876b1a2fe56edd86e9d06fc6f2cfda`.
- Ran `env LEAN_NUM_THREADS=2 lax build . --replay --no-color`, session
  `30985`. Layout and dependency resolution passed; concepts compiled in 33s.
  Source inspection then established that the current Lax62 reader has
  migrated from Lax865980Proofs to Lax67Proofs. Lax842588 still requires Lax865980 command
  types. Interrupted this run with Ctrl-C (terminal exit 130) while the new
  dependency compiled; no completed proof-build or replay claim is made.
- Identified a bounded compatibility option: preserve only the old array
  reader and required lemmas, with upstream attribution, in Lax842588Proofs;
  mechanically update callers and remove the Lax62 dependency. Asked the
  user for approval; no proof implementation changes made yet.
- Confirmed Lax842588 has no Git remote. Asked whether to create public
  `szymtor/lax53` or use another URL. No public repository or submission
  request was created. Existing dirty implementation and staged rename
  remain preserved. Whitespace and a source credential-pattern scan passed.
- Next: obtain these choices, implement the proof-only compatibility fix if
  approved, rerun full validation/replay, commit/push, submit, and monitor the
  Archive result. Never register.

### Preview refresh request

- Confirmed local Lax842588 pages respond on ports 8123 and 8125 (network checks
  require escalation in this sandbox); opened http://localhost:8125/lax-842588/.
- `build-output.json` remains dated September 3 at 22:51. Did not modify or
  fabricate generated validation output. Refreshing it to current source
  still requires the compatible reader fix and a successful full Lax build.

## 2026-09-05 — Approved reader localization and concept consolidation

- User approved localizing the small reader while preserving the theorem,
  encoding, and Lax865980 RAM model. Added `Lax842588Proofs.ArrayInput` with only the
  unchanged list helpers and array prelude from upstream commit `363928968...`,
  with source and Apache-2.0 attribution. Mechanically changed 19 caller files,
  imported the helper in the root, and removed the Lax62Proofs requirement.
- Added `tests/ArrayInput.lean` and included it in the intrinsic-compiler
  regression script. The standalone test passed (session `71748`): exact
  command syntax, empty/nonempty inputs, preserved suffix, 12*n+6 cost,
  write-frame simp lemmas, and only the three background axioms.
- Full build `42344` resolved only mathlib/Lax865980/Lax146103/Lax560851 and compiled
  concepts. It was interrupted (exit 130) before completion when the user
  requested merging TreeAutomataToMSO, MSOToTreeAutomata, and
  MSOTreeAutomataEquivalence before submission.
- Consolidated the three unchanged statement types in
  `concepts/Lax842588/MSOTreeAutomataEquivalence.lean`, including their shared
  explanation; removed the two redundant concept files, recoverable in Git.
  Proof implementation modules remain separate. Updated imports and the two
  moved statements' conclusion annotations. Added the three-type regression
  `tests/TreeAutomataEquivalence.lean`.
- Restarted full Lax validation/replay as session `52973`; layout, resolution,
  and concept compilation (20s) passed. Await proof compilation/replay before
  claiming the preview refreshed. No submission or registration performed.
- Explained the source-language route in response to the user's question:
  Lean functions proved primitive recursive → finite seven-constructor Code
  → verified IMP+ compilation → Lax865980 word-RAM. This is not a general Lean
  compiler or an efficiency claim for parameter-only compilation overhead.
- The merged-concept regression passed, session `40973`: all three existing
  proof types are definitionally equal to the statements in the single concept.
  The user repeated the preview refresh request; continued the same full build
  `52973`, without restarting it or mislabeling the old preview as current.
- Later inspection found the host Lax pipeline hardcodes
  `LEAN_NUM_THREADS=4`; the requested outer thread cap was ineffective.
  With a memory-heavy rebuild still progressing slowly, interrupted `52973`
  (exit 130), then started `env LEAN_NUM_THREADS=1 lake build Lax842588Proofs`
  as session `35412`. It reuses already-built modules and has reached
  3103/3153 tasks. This is compilation, not independent kernel replay;
  rerun full Lax validation after this terminal build result. The preview
  still has not been refreshed and no submission has been made.
- Single-threaded proof-root build `35412` completed successfully (3153 jobs),
  including `IntrinsicUniformModelChecking` and `FixedSentenceModelChecking`.
  Started final `lax build . --replay --no-color` using the completed cache;
  await that terminal result and preview emission before claiming refresh.
- Replay-enabled Lax run `43312` passed layout, resolution, concept compilation
  (6s), and cached proof compilation (3s). Its independent full-package
  `leanchecker Lax842588Proofs` process was still active after roughly 19 minutes,
  with no verdict. Interrupted the run (exit 130) to prioritize the user's
  repeated preview request via the standard local pipeline.
- Started `lax build . --no-color` as session `98332` (no optional independent
  replay; normal Lean compilation and Lax inspection still apply). Full replay
  remains outstanding before submission; do not call it passed.
- Started six direct Lean regressions sequentially, session `71294`: reader,
  merged concept, internal compiler bridge, public compiler, parameter bounds,
  and fixed-sentence theorem. No overlapping proof rebuild is launched.
- Standard Lax validation `98332` passed in 1m16s: 10 concepts, 15 annotated
  proofs. Both MSO headlines and all three merged-equivalence statements have
  empty non-background assumptions. Six informational dependency warnings only.
- Preview output refreshed September 5 at 22:17. Confirmed port 8125 lists
  the merged concept and both headlines, omits the two removed direction
  concepts, and opened the page in the user's browser.
- User then explicitly requested commit and submission. Announced public
  `szymtor/lax53` and draft submission, with mandatory replay performed by
  the Archive. Read-only GitHub check confirmed the repository does not yet
  exist. Publication is authorized; never register. Source credential-pattern
  scan and whitespace check passed before staging.

## 2026-09-05 — Tree-automata terminology

- The user interrupted publication preparation to ask which terminology is
  more commonly used and to adapt the abstract and submission comments.
- Literature check favors "tree automata" as the conventional default, not
  a claim based on search-engine hit counts. Gécseg–Steinby's book is titled
  *Tree Automata* (https://arxiv.org/abs/1509.06233); Laurent Doyen's course
  uses *Tree Automata and Applications*
  (https://lsv.ens-paris-saclay.fr/~doyen/teaching/taa.html). The longer term
  is also established: TATA's chapter/exercise heading is "Recognizable Tree
  Languages and Finite Tree Automata"
  (https://home.lmf.cnrs.fr/LucLapointe/TATA).
- Updated the abstract, submission title, five concept files' prose/titles,
  and one proof module's introductory comment. Use "tree automata" as the
  default; explicitly say "with finitely many states" where the assumption
  matters, and retain "finite ranked trees" for the input domain. Clarified
  that the underlying general Lean structure permits arbitrary state types,
  while recognizability and the main theorems require finite state sets.
- No Lean declaration, statement, proof, identifier, or bibliography title
  changed. Compared all six edited Lean files after erasing comments: their
  non-comment content is identical. Whitespace check passed. No expensive
  rebuild launched for this wording-only request; preview needs regeneration
  before publishing the revised wording.
- Confirmed prior six-file regression process `71294` completed successfully
  (exit 0). No process from that test run remains active.
- No commit, public repository, or Lax submission was created before the
  interruption, and none was made as part of this terminology-only task.


## 2026-09-15 — Lean 4.33 migration, continued

All upstream drafts are published and dependency pins updated. Concepts build,
full structural certification and certificate report pass. All ten concept
sources exactly match published original 91e66a9f14c67cf1baac7cf711ff80bb11f78965
after namespace migration. PrimitiveRecursiveBridge regression passed after
updating expected message wrapping, preserving the axiom set.

Proof migration uses using!, local backward.isDefEq.respectTransparency false,
explicit list/index simplification hypotheses and removal of redundant final
tactics. Public compiler, materialization, formula input and tree-automata
equivalence modules now build. Full proof build, headline regressions, kernel
replay and publication remain pending. Logs live under ../migration-tools.
Original drafts and main branches are untouched; no registration performed.


### Validation completed

Full proof build passed (3218 jobs). All eight named regressions, structural
certification and certificate report pass. Full Lax replay passed: kernel
37m53s, total 38m17s, 10 concepts and 15 annotated proofs. Nine proof assumption
lists are empty; six reference four already-proved canonical-encoding concepts.
Checked each against the published dependency's assumption-free proof records.
Both headline MSO runtime theorems have empty assumption lists. No unresolved
mathematical assumptions remain. The 343 inherited unused helpers are retained
intentionally alongside two proof-package and four draft-package warnings.
Publication of the independent draft remains next; no registration.


### Publication completed

Published https://laxarchive.org/lax-842588/ as an independent Lean 4.33 draft.
Archive issue 115, workflow 34950409101, source commit
828f03cc85308eb60ba345b0c815310157600f70 on szymtor/lax53 branch lean-4.33.
Archive rebuild 23m27s; publication 57s. All six requested migration drafts are
now public. Original drafts and main branches preserved; none registered.

## 2026-09-15: correction to the public RAM model

The user identified `Lax808846.Ram` as the required RAM. It retains dedicated
input/output tapes, adds immutable indexed input and EOF/length operations,
and charges terminal instructions. The old `lax-865980` package was deleted
upstream. Root coordinates replacing that dependency with the pure machine
definitions and checked IMP machinery vendored into the RAM/Turing proof
package as `Lax759944Proofs.Legacy`.

Added `CheckedRamAdapter.lean`, importing the checked instruction embedding
`Lax759944Proofs.LegacyRamBridge`. The adapter lifts a legacy execution bound
`T` to any new bound at least `T + 1`. Changed the four public wrapper proofs
in `AutomatonLinearTime`, `IntrinsicUniformModelChecking`, and
`FixedSentenceModelChecking` to choose the embedded program and a time
coefficient larger by one. The uniform MSO coefficient remains computable
by composition with successor. Input encodings, output lists, word widths,
and workspace capacity assumptions stay unchanged. Expanded legacy
implementation theorems remain inspectable proof-side intermediates.

Updated five regression files to use the vendored namespace, and imported
the adapter in the proof root. No scripts referenced the old namespace.
The adapter independently compiles under Lean 4.33 using the bridge check
overlay and installed mathlib package paths; output
`/private/tmp/CheckedRamAdapter.olean`. Full endpoint builds, prescribed
regressions, Lax validation, and independent kernel replay are pending the
coordinated dependency update. This correction has not been published or
registered.

The focused endpoint build is running with local package overrides:
`env LEAN_NUM_THREADS=2 lake --packages=../../migration-tools/ram-808846-local-overrides.json build Lax842588Proofs.CheckedRamAdapter Lax842588Proofs.AutomatonLinearTime Lax842588Proofs.IntrinsicUniformModelChecking Lax842588Proofs.FixedSentenceModelChecking`.
Log: `../migration-tools/trees-808846-endpoints.log`. The adapter and both
corrected public statement modules have passed. An independent adapter axiom
audit passed: the transfer theorem uses `propext` and `Quot.sound`; its
arithmetic bound uses those and `Classical.choice`. Log:
`../migration-tools/trees-808846-adapter-audit.log`.

### RAM correction: structural regressions and implementation notes

Both `CertifiedRepresentations.lean` and `CertificateReport.lean` pass with
`lake --packages=../../migration-tools/ram-808846-local-overrides.json env lean`
from `concepts/`. Log: `../migration-tools/trees-808846-certification.log`.
This is local Lean validation against the corrected dependency graph, not
full Lax validation or independent kernel replay. The focused endpoint build
is still running. `IMPLEMENTATION_NOTES.md` now names the public
`Lax808846.RamComputes.ComputesInTime`, the internal vendored compiler, the
checked witness embedding and terminal charge, and the localized reader.
The obsolete Lax-62 dependency claim has been removed.

### RAM correction: early implementation regressions

`ArrayInput.lean`, `IntrinsicCompilerBridge.lean`, and
`TreeAutomataEquivalence.lean` pass with the same explicit local overrides.
The checks cover the localized input reader, compiler/materialization
interfaces, and the unchanged logical equivalence statement types. Logs:
`../migration-tools/trees-808846-array-input.log` and
`../migration-tools/trees-808846-early-regressions.log`. The endpoint rebuild
and remaining headline/primitive-recursive regressions are still pending.

The focused `Lax842588Proofs.PrimitiveRecursiveAutomata` build and
`PrimitiveRecursiveBridge.lean` regression also pass with the correction
overrides; log: `../migration-tools/trees-808846-primitive-regression.log`.
The local build reports 3060 jobs, predominantly cached dependency replays.

### RAM correction: all public endpoint proofs and regressions pass

The selected corrected endpoint build passes all 3198 jobs, including
`AutomatonLinearTime`, `IntrinsicUniformModelChecking`, and
`FixedSentenceModelChecking`. No additional endpoint proof edits were needed.
`IntrinsicPublicCompiler`, `IntrinsicParameterBounds`,
`FixedSentenceModelChecking`, and `RamComplexityStatements` all pass with
the same explicit local overrides. Combined with the earlier tests, every
prescribed implementation/equivalence regression and both structural
certification checks now pass. The MSO headline axiom guards remain
background-only; all four public RAM proofs match their exact concept types.
Logs: `trees-808846-endpoints.log`, `trees-808846-public-compiler.log`, and
`trees-808846-endpoint-regressions.log` in `../migration-tools/`.

The full `Lax842588Proofs` root build is running separately with the explicit
local overrides; it includes the retained helper inventory beyond the
selected headline dependency graph. Archive revision pinning, full Lax
validation, independent kernel replay, and publication of this correction
remain pending the coordinated corrected dependency releases.

### RAM correction: complete local proof package passes

The full `Lax842588Proofs` root build completed successfully (3222 jobs)
with `env LEAN_NUM_THREADS=2 lake
--packages=../../migration-tools/ram-808846-local-overrides.json build
Lax842588Proofs` from `proofs/`. All retained helpers remain present. Log:
`../migration-tools/trees-808846-full-proof.log`. Together with the selected
endpoint build, all eight implementation/equivalence regressions, the
structural certification test and the certificate report, this completes
the local Lean checks for the correction. No registration or publication
has been performed by the tree agent. The next action is to pin the actual
corrected RAM/Turing and canonical archive revisions and run full Lax
validation with independent kernel replay against those exact pins.

### 2026-09-16: prepare the exact corrected RAM dependency pin

Updated the proof package requirement for `Lax759944Proofs` to
`7010243df12cdda03abc5f63ec8de2c0963d4052`. The RAM/Turing revision passed
full local Lax validation and independent kernel replay with seven concepts,
four annotated proofs, and empty assumption lists; its commit is pushed and
the Archive draft update is in progress. All canonical dependencies remain
at `091d4fe67804863dac4001f7bc1ac72d8597a7e4` pending the corrected canonical
release revision. No builds, commits, pushes, or registration were performed
for this preparation. Existing local tree proof and regression results remain
complete. Exact dependency validation and replay await the corrected canonical
pin and completion of the upstream Archive draft updates.

### 2026-09-16: prepare the exact corrected canonical dependency pins

Pinned all three tree requirements for `Lax560851` and `Lax560851Proofs`
to `8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b`. The canonical revision passed
full Lax validation and independent kernel replay in 7m08s: 12 concepts and
18 annotated proofs with empty assumption lists. Its commit is pushed,
and the Archive draft update is still in progress. The RAM/Turing pin
remains `7010243df12cdda03abc5f63ec8de2c0963d4052`; the MSO-word pin remains
`b7b157e93741492b33a0fa84ec76e24a571e2a98`.

The exact-pin tree replay command is prepared in `CURRENT_STATE.md` and will
write `../migration-tools/trees-808846-validation.log`. It must wait for
confirmation that the Archive accepted the corrected canonical revision.
It will include the coordinator's prose-only updates from Lax-13/Lax-58 to
Lax808846/Lax560851 in `concepts/Lax842588/MSOLinearTime.lean` and the RAM
instruction reference in `abstract.md`. No code changes, builds, commits,
pushes, or registration were performed for this pin preparation.

### 2026-09-16: canonical Archive dependency gate failed

Read-only monitoring of canonical Archive run
https://github.com/lax-archive/lax/actions/runs/35064198245 found the
`Validate` job failed its `Static gate` at 06:33:42 UTC. The submit log
`../migration-tools/canonical-808846-submit.log` reports two
`dependencies / draft-dependency` errors for `Lax759944` and
`Lax759944Proofs`: the remote validator admits only registered dependencies.
Publication jobs were skipped; canonical revision
`8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b` was not published.

The local CLI specification read during preparation explicitly admits draft
dependencies with a warning, and canonical local validation/replay had passed.
This is a difference between the local and Archive validation policies, not
a reported Lean proof failure. The tree exact-pin replay was not started.
No registration was attempted. The coordinator was notified with the failed
job identifier `104690889459` and the exact diagnostic; tree replay awaits
resolution and confirmed canonical Archive acceptance.

### 2026-09-16: keep drafts and finish independent local validation

The user explicitly chose to keep the submissions as drafts and declined
registration. No registration or further Archive publication will be
attempted, and no approval remains pending. The canonical pin stays at
`8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b`; exact-pin tree Lax validation
cannot proceed while the Archive has not accepted that revision.

A final-source local `Lax842588Proofs` build is running with the existing
explicit local overrides, logged separately in
`../migration-tools/trees-808846-local-final-build.log`. It will be followed
by stock `leanchecker --verbose Lax842588Proofs` in the same Lake environment
with `LEAN_NUM_THREADS=2`, logged in `trees-808846-local-kernel.log`. This
will be direct local proof validation, not a substitute Archive verdict.
The checker does not implement `--help`; an exploratory help invocation
started replaying the default module and was interrupted (exit 130). That
interrupted invocation is not validation evidence. The final checker run
will start only after the complete local build succeeds.

After those local checks, the coordinator will commit/push the corrected
tree source as a reviewable branch. The tree agent will not commit, push,
register, or submit it.

### 2026-09-16: extend final local replay to both package roots

The final local validation sequence now builds both `Lax842588Proofs` and
`Lax842588`, then runs the fresh annotation audit in
`../migration-tools/trees-808846-final-audit.lean`. That audit checks all 15
tree proof/statement pairs and their exact non-background axiom sets
(nine empty and six using four canonical encoding statements), plus the
four corresponding canonical discharge proofs and their empty axiom sets.

After the audit, one stock kernel replay will select both prefixes with
`leanchecker --verbose Lax842588 Lax842588Proofs`, using the same explicit
local overrides and `LEAN_NUM_THREADS=2`. This replaces the planned
proof-only replay. Its expected coverage is 173 modules: ten concept
modules and their root, plus 161 proof modules and their root. The run will
be checked against the current source inventory. This remains direct local
validation; the blocked exact-pin Lax/Archive pipeline will not be run.

### 2026-09-16: final local validation complete; retain drafts

The final-source proof root build passed all 3222 jobs in 2832.4s (47m12s),
and the concept root passed all 960 jobs in 11.6s. The checks used the
explicit local overrides in `../migration-tools/ram-808846-local-overrides.json`.
Logs are `trees-808846-local-final-build.log` and
`trees-808846-local-concepts.log` in `../migration-tools/`.

The fresh annotation audit passed for all 15 tree theorem/statement pairs
and their exact non-background axiom sets: nine empty sets and six sets
using the four canonical encoding statements. All four canonical discharge
proofs have matching public statement types and empty non-background axiom
sets. After the initial successful audit, its per-proof logging interpolation
was corrected without changing any assertion. The named audit passed again
in 18.7s and lists all 19 checked proofs in
`../migration-tools/trees-808846-final-audit.log`; the initial log is retained
as `trees-808846-final-audit-initial.log`.

The single stock Lean 4.33.0 kernel replay
`leanchecker --verbose Lax842588 Lax842588Proofs` passed (exit 0) in 1771.0s
(29m31s), with `LEAN_NUM_THREADS=2` and the same explicit local overrides.
Its log contains exactly the 173 expected unique modules: ten concept
modules plus their root and 161 proof modules plus their root. No source
module is missing and no extra module was replayed. All 179 captured source
and configuration file hashes match before and after validation. Evidence:
`trees-808846-local-kernel.log`, `trees-808846-validated-source-hashes.json`,
and `trees-808846-validated-source-hashes-after.json` in `../migration-tools/`.

The ignored `lake-manifest.json` cache files still contain the retired
dependency; the explicit override superseded them for every final check.
No cache manifests were regenerated. Ordinary Lake commands require updated
manifests first; all tracked source and lakefiles already use the corrected
dependencies.

This completes direct local validation of the corrected source. It is not
Archive acceptance or completion of the blocked exact-pin Lax pipeline.
The user chose to retain drafts and declined registration, so no registration
or further Archive publication was attempted. Canonical pin
`8ec635640f3fd05271fa5cb7b1d3ae9e59400d7b` and RAM/Turing pin
`7010243df12cdda03abc5f63ec8de2c0963d4052` remain unchanged. The corrected
tree branch is ready for the coordinator's commit/push; the tree agent has
performed neither action.


## 2026-09-16 — Nine-claim interface implemented; local preview before submission

User authorized the agreed cleanup and required a local preview before
submission. Six axioms and their proof annotations were removed: formula/tree
structurality, both input-length statements, fixed-automaton acceptance, and
fixed-sentence model checking. All six results remain ordinary helper theorems.
The existing existential determinization statement remains unchanged.

Abstract complementation now uses public determinization. The equivalence
proof uses both public directional statements. The fixed-automaton helper
specializes public uniform acceptance and absorbs the automaton workload in
the coefficients; unfolding `WordArena.encode` establishes the identical
physical input tape. The tree-only fixed-sentence theorem retains its direct
checked implementation. No generic input-specialization theorem was added.

Validation used `LEAN_NUM_THREADS=2` and the existing explicit local package
overrides. The concept root passed (960 jobs). The first full proof build
identified the missing encoding unfold in the fixed-automaton helper; after
that correction the full root passed (3222 jobs). Five focused regressions
passed: CertifiedRepresentations, TreeAutomataEquivalence, IntrinsicParameterBounds,
FixedSentenceModelChecking, and RamComplexityStatements. The test changes
check the demoted helpers' original full types and preserve exact axiom guards;
the logical test also guards the new public dependency edges.

`../migration-tools/trees-interface-audit.lean` checked all nine retained
proof/conclusion types and exact axiom sets, plus four canonical discharge
proofs. The local split is four empty and five nonempty sets; the canonical
proofs have empty non-background sets. Fresh official Lax static/inspection
phases passed with zero violations and found ten concept modules, nine public
statements, and nine annotated proofs. The 362 unused-helper warnings reflect
retained implementation lemmas. No independent kernel replay was repeated for
this interface change; prior RAM-rebase replay is recorded separately.

Preview generation uses `../migration-tools/trees-interface-preview.mjs` and
the official inspector/judge/emitter. Its development-only output has no
capture or local-build acceptance metadata. The separate preview server uses
the official Lax renderer with the corrected canonical and RAM/Turing local
draft outputs substituted in memory; no Archive records are changed. The
sandbox initially blocked listening on the preview port; the authorized
escalated server start succeeded.

Preview: http://localhost:8138/lax-842588/#proof-network . The URL was opened
through the OS. HTTP/HTML and network data checks confirm nine proven local
statements, nine proofs with zero outstanding assumptions, all ten concept
pages, and the corrected `Lax808846` canonical RAM page. Browser automation
could not initialize because an installed service-module path was missing;
no automated visual check is claimed. The server is left running for review.

Logs and reports are in `../migration-tools/trees-interface-*`, including
`proof-build-final.log`, `regressions.json`, `audit.log`, `inspection.log`, and
`preview-verification.json`. Source/artifact hashes accompany the preview.
Changes are uncommitted. No submission or registration occurred. Next action:
user review of the local preview; normal publication still has draft-dependency
blockers.


## 2026-09-16 — Local proof-network rendering repair

The user reported four `fixed-position: Fixed port offset is outside its
measured node` diagnostics. The installed Lax renderer rounded port coordinates
to 0.001px but calculated the containing envelope separately. Valid fractional
metrics can therefore put the rounded port outside its envelope (for example
100.016 versus 100.01599999999999); separate rounding can also differ by 0.001px.

Added a scoped local preview fix in `../migration-tools/graph-port-envelope-fix.mjs`:
reserve the maximum of the computed node bounds and its rounded port positions.
The preview server applies it to the generated `graph-node-size.js` after every
render. No installed renderer files, Archive records, Lean sources, statement
data, or proof dependencies were changed. The strict geometry validator and
port coordinates are unchanged. The server was restarted on port 8138.

`check-graph-port-envelope.mjs` reproduces the original failure, then validates
3000 fractional metric cases and four real graph views. The in-app browser
integration still could not initialize (missing installed service module), so
an isolated headless Chrome test used Playwright Core 1.62.1 installed under
`../migration-tools/graph-preview-check`. Its temporary profile is separate
from user browser state; requests were restricted to localhost.

Chrome 152.0.7977.84 rendered the original main page successfully: this defect
depends on browser/font metrics. The patched browser run passes all eleven
tree pages and thirteen graph containers, with no page errors. Its main proof
network screenshot is byte-identical to the original successful Chromium
screenshot. The regression covers the fractional metrics which triggered the
failure in the original sizing code. Browser report and screenshots are under
`../migration-tools/graph-preview-*`; the geometry regression log is
`../migration-tools/graph-port-envelope-test.log`.

The repaired preview remains at http://localhost:8138/lax-842588/#proof-network .
Next action remains user review before submission. Nothing was submitted or
registered; no Lean rebuild was needed for this renderer-only repair.
