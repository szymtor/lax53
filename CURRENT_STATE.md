# Registered final submission — lax-842588

Updated 2026-09-16. [Public submission](https://laxarchive.org/lax-842588/).
Frozen source: `7790103f255ce90a858c51d10ad858b4b230f8b9` on
`szymtor/lax53:lean-4.33`. Author credit is `GPT 5.6`.

The user reviewed the local preview and explicitly authorized publication and
permanent registration of the six current Lean 4.33 submissions. This
supersedes earlier keep-draft restrictions. The six older drafts are unchanged.

## Final mathematical interface

Nine public claims remain: determinization; both MSO/automata directions and
their equivalence; finite value translations; tree and sentence round trips;
uniform automaton acceptance; and uniform MSO model checking.

Formula/tree structurality, both input-length facts, and both fixed-parameter
runtime results remain ordinary proof-package lemmas. Complementation uses
public determinization; equivalence uses the two public directional contracts.
The fixed-automaton helper specializes uniform acceptance. The tree-only
fixed-sentence helper retains its checked direct implementation.

The public RAM predicates use Lax808846 with dedicated immutable input and
append-only output tapes. All four dependency sources are registered:

| Dependency | Frozen commit |
| --- | --- |
| MSO words, lax-146103 | `a850aa03d9cb3bff8aec3990269c99942ac56aff` |
| Canonical encodings, lax-560851 | `2748fdc0afc0b4f729b7775ca6475ba08129418a` |
| RAM/Turing, lax-759944 | `134e398cef46599371df99f10c9007bc34ba3868` |
| RAM model, lax-808846 | `9394e531cc51cb67a0214bca3f9264dfe97ba5c7` |

## Completed validation and publication

- All 173 Lean sources match the reviewed preview. Its five focused regressions
  and exact type/axiom audit passed before publication.
- Full exact-pin local Lax build and independent kernel replay passed: 66m55s
  total, including 58m55s replay; ten concepts and nine annotated proofs.
- Independent Archive workflow
  [35085094609](https://github.com/lax-archive/lax/actions/runs/35085094609) passed.
  A CLI transport timeout was recovered by reattaching to the same run.
- Fresh local and accepted Archive inputs, dependency lists, all concept
  records, and all nine proof records match exactly. Every public claim has
  a closed proof through the registered dependency network.
- [Registration workflow 35091939469](https://github.com/lax-archive/lax/actions/runs/35091939469)
  succeeded. All six current submissions are registered and verified.
- Evidence: `../migration-tools/finalize-trees-build.log`,
  `finalize-trees-submit.log`, `finalize-trees-submit-resume.log`,
  `finalize-trees-register.log`, and `finalize-all-records-verification.log`.

Lax regenerated both package manifests from accepted exact pins. Ordinary
Lake commands now work without the earlier development override.

The local preview renderer workaround is in
`../migration-tools/graph-port-envelope-fix.mjs`; it is separate from the
Archive submission. The user requested no developer bug report.

**Next action:** none for this release. The registered source is immutable;
future mathematical changes require a new submission. Documentation branches
may advance without changing the frozen release. See [WORKFLOW.md](WORKFLOW.md)
and [SESSION_HISTORY.md](SESSION_HISTORY.md) for details and prior history.
