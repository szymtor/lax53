# Formalization state

Read this file first when resuming work. Update it at the end of every session.

## Submission

- Lax id: `lax-53`
- Lean namespace: `Lax53`
- Proof namespace: `Lax53Proofs`
- Working title: `MSO-automata-trees`
- Current phase: concept elicitation (no Lean concept has been authored yet)

## Intended result

The precise source statement has not yet been supplied. The repository name
suggests a result involving monadic second-order logic, automata, and trees,
but no definition or theorem will be inferred from that name alone.

Needed from the user before concept authoring:

- the exact theorem/result to formalize, preferably as source text or a paper
  reference with theorem number;
- the intended variants of trees, automata, and MSO semantics;
- any scope boundary (one headline theorem versus supporting definitions and
  lemmas).

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
- Blocked concept authoring on the missing mathematical source statement.

## Exact next action

Obtain the precise intended result from the user. Then inspect the relevant
mathlib and Lax archive APIs, author the minimal concept modules under
`concepts/Lax53/`, import each from `concepts/Lax53.lean`, update the manifest
and abstract, and iterate on `lax build . --only concepts` until clean. Stop
there for the user's semantic review.
