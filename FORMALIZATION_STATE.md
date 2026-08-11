# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-53`
- Lean namespace: `Lax53`
- Proof namespace: `Lax53Proofs`
- Working title: `MSO-automata-trees`
- Current phase: extensional formalization complete; effectiveness proof
  development resumed at the user's request

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

## Exact next action

Implement the explicit automaton-code-to-MSO compiler first, specialize the
existing run-formula correctness theorem to it, and prove computability. Then
refactor the converse marked-formula induction to produce finite automaton
codes and derive serialization corollaries. Registration remains user-only.
