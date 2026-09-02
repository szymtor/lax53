# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-53`
- Lean namespace: `Lax53`
- Proof namespace: `Lax53Proofs`
- Working title: `MSO-automata-trees`
- Current phase: coordinated Lax-58 structural-representation revision
  complete locally; concept and proof roots pass; full Lax validation is
  blocked only by the unresolved local-draft dependency record

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

### 2026-09-02

- Implemented the reviewed Lax-58/Lax-53 boundary. Lax-53's mathematical
  equivalence now quantifies direct value-level translations between finite
  automaton data and inductive raw formulas; it no longer mentions binary
  serialization or an existential codec package.
- Added `StructuralRepresentations.lean`. It gives explicit named structural
  presentations for ranked alphabet codes, transitions, automata, formulas,
  sentences, and ranked trees using the fixed Lax-58 vocabulary. Three grouped
  certificate statements assert combinator lawfulness, complete formula
  constructor equations, and complete ranked-tree constructor equations.
- Tightened the ranked-tree representation after review: the unique tree
  constructor uses a fixed tag, while the symbol number is an explicit
  `Nat` field and children occur recursively in their finite-index order.
- Added and compiled proofs for all structural certificate statements and the
  two value-level translation directions.
- Removed the obsolete formula token serializer/parser and its coding-specific
  computability proof modules. Retained numeric finite-automaton operations
  because they implement the reverse compiler and the RAM evaluator.
- Revised `MSOLinearTime`: the sentence is fixed outside the measured
  execution, so preprocessing is uncharged; runtime-input preprocessing would
  have to be included. The public theorem does not impose an unrelated hidden
  formula coding merely to state `Computable`.
- `lake build Lax53Proofs.MSOLinearTime` succeeds through 3022 jobs, and the
  final `lake build Lax53Proofs` succeeds through 3038 jobs after root-import
  cleanup. `lake build Lax53` succeeds through 909 jobs.
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

### 2026-09-01

- Began the user-requested refactor of the effectiveness layer to use the
  generic codec vocabulary from `lax-58` instead of exposing a hand-written
  prefix formula parser and constructor tags.
- The proposed `EffectiveTranslations` concept now treats raw formulas as
  inductive syntax, existentially chooses canonical and effective codecs for
  automaton bodies, alphabet--automaton inputs, and alphabet--sentence inputs,
  and states both translations using `Lax58.CanonicalCodec.Codec.ComputableMap`.
- Kept the fixed-width natural-word automaton table only in
  `TreeModelCheckingEncoding`: its layout is intrinsic to the constant-time
  random-access algorithm and its runtime bound, not the generic
  serialization. Formula preprocessing no longer exposes a word layout.
- Updated the MSO linear-time concept so effectiveness of compilation and of
  its coefficient is expressed through the same hidden serialization.
- The changed concept modules were syntax-checked successfully against the
  locally built `lax-58` artifacts without changing Lake's generated manifest.
- Blocking validation fact: `lax-58` is still in Archive state `init`, has no
  source record and no Git remote, so `lax-53` cannot yet add the required
  Archive-pinned dependency or run an ordinary Lax concept build. The next
  action after concept review is to publish `lax-58` as a draft, pin its exact
  source in both `lax-53` packages, and only then adapt the proofs.

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

- Reserved and scaffolded `lax-53`.
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
- Confirmed `lax-52` is still in the archive's `init` state, so `lax-53`
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
  `Lax53Proofs/Determinization.lean`; the annotated conclusion is detected by
  Lax.
- Refined ranked-tree navigation: `Node.child` is now defined directly in the
  `RankedTree` concept and `Node.ChildAt` is the corresponding direct indexed
  relation. This matches the earlier decision that node navigation is
  tree-intrinsic and avoids a dependent-index ambiguity in the former
  inductive relation. The concepts and dependent proof modules compile.
- Added reusable node lemmas (`ChildAt` functionality and every non-root node
  has a parent) and generic derived MSO semantic simp lemmas.
- Completed `Lax53Proofs/TreeAutomataToMSO.lean`. The constructed sentence
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
- Final validation after cleanup: `lake build Lax53Proofs` completed all 915
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
  the archive-standard word RAM `Lax13.Ram` at registered commit
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
- The word-length conditions follow the established Lax13/Lax11 convention:
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
  `http://localhost:8125`; it includes `lax-53` and 23 published submissions.

## Historical implementation notes

The user approved proof work for every remaining theorem and authorized
strengthening the automaton coefficient when concrete. The automaton concept
now states the explicit bound `C (|M| + 1)^2 |t|`; this compiles.

Proof work in progress:

- Added the pinned `Lax13Proofs` dependency so the verified IMP+-to-word-RAM
  compiler can be used. Provisioning succeeded outside the sandbox.
- Added `Lax53Proofs.EffectiveTranslations`: canonical raw-formula serializer,
  parser round-trip, and a concrete automaton-to-MSO compiler. Its elaborated
  formula is proved equivalent to accepting runs. A separate token-level
  implementation is proved primitive recursive and extensionally equal to
  the semantic compiler, completing the automaton-to-MSO half of uniform
  effectiveness (including alphabet preservation and language preservation).
- Added `Lax53Proofs.EncodedAutomatonEvaluation`: a sparse pure evaluator and
  a complete proof that its reachable-state list is exactly
  `Automaton.RunsTo`, hence its Boolean result decides acceptance.
- Added `Lax53Proofs.FiniteAutomatonEncoding`: a complete finite-table
  serializer, proved semantically exact. Its serializer is primitive recursive
  uniformly when the alphabet, state bound, transition test, and acceptance
  test all depend on an encoded input. This is the reusable bridge for the
  explicit finite automata in the reverse MSO translation.
- Added `Lax53Proofs.EncodedAutomataOperations`: numeric lookup, state
  renaming, product/intersection, bitset determinization, complement, union,
  projection, and pullback definitions. State renaming, intersection,
  canonical powerset determinization, complement, and union now have complete
  semantic proofs. The powerset transition was tightened to require the
  canonical `Encodable.encode` of its subset, avoiding noncanonical aliases
  admitted by a raw `decode` test. The target build passes.
- Added `Lax53Proofs.EncodedProjection`: rank-preserving relabeling of trees
  and both directions of the semantic projection theorem, culminating in an
  acceptance iff an accepting source relabeling exists. The target build
  passes.
- Added `Lax53Proofs.MarkedAlphabetEncoding`: an explicit executable
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
  language-preserving compiler functions. The proof root `Lax53Proofs.lean`
  typechecks, and a source audit reports no `sorry` or `admit`.

At that checkpoint, remaining theorem work was sharply separated:

1. Prove the intensional mathlib `Computable compileSentence` certificate.
   Executability alone does not discharge this predicate. The clean route is
   a fuel-bounded token parser/compiler carrying an explicit validity bit,
   together with primitive-recursive closure proofs and extensional equality
   to `compileSentence`.
2. Implement and verify the uniform word-RAM program. The pure sparse
   evaluator is already proved correct, but the RAM axioms quantify an actual
   `Lax13.Ram.Program`; the generic Lax11 tree-fold theorem is non-uniform in
   its table and therefore cannot directly prove the current uniform-input
   statement.

Checkpoint validation: `lake build Lax53Proofs` passes. There are no
`sorry`/`admit` placeholders in `proofs/Lax53Proofs`; the remaining unproved
submission claims are the concept axioms for uniform effectiveness and the two
RAM bounds, whose proof theorems have not yet been completed.
Registration remains user-only.

## Current completion checklist

- Lax-58's full `lax build . --no-color` passes with the revised structural
  architecture and proofs.
- Lax-53 targeted builds pass for its revised concepts, structural proofs,
  value translations, automaton RAM theorem, and fixed-sentence MSO theorem.
- `lake build Lax53` passes (909 jobs) and `lake build Lax53Proofs` passes
  (3038 jobs). The remaining output consists of non-fatal Lean linter warnings
  in older helper proofs.
- A full Lax-53 `lax build` is currently blocked at dependency resolution by
  the installed CLI's demand for an Archive record for Lax-58, even though
  direct Lake builds honor the generated local override.
- The preview remains the last successful pre-refactor Lax build until that
  resolver issue is removed; do not describe it as validating the revision.
- The abstract and equivalence concept attribute the tree result to Thatcher
  and Wright (1968), independently Doner (1970); both full references and DOI
  links were verified in the earlier preview.
- Registration remains user-only.
