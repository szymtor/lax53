# Structural RAM implementation notes

This note records the implementation boundary for the coordinated canonical
encoding and tree submissions, now Lax-560851 and Lax-842588. References to
Lax-58 and Lax-53 below identify their original drafts. It is not a concept
module.

## Removed serialization surface

Lax-58 no longer exposes the former binary-codec modules:

- `CanonicalCodec`;
- `CanonicalDecoding`;
- `CodecCombinators`;
- `ComputableMaps`;
- `EffectiveCombinators`;
- `FiniteCollections`;
- `LawfulCombinators`;
- `PrimcodableCodec`;
- `PrimitiveCodecs`;
- `StructuralEncoding` and `StructuralEncodingLaws`.

Their associated proof modules were removed with them. Lax-53 also removed
the in-place raw-formula token serializer/parser and its coding-specific
computability obligations. The mathematical value translations remain; they
do not prescribe a binary interchange format.

## Distinguished input

For a structural value `raw`, Lax-58 builds the explicit dense three-word
postorder arena `WordArena.encodeRaw raw`. The only physical input admitted by
the Lax-53 runtime theorem is

```text
[root, memory[0], memory[1], ..., memory[m - 1]]
```

namely `(WordArena.encodeRaw raw).toInput`. For automaton acceptance, `raw` is
the named two-field constructor `automatonAcceptance(automaton, tree)`, whose
fields use the constructor-certified Lax-53 structural representations.
For uniform MSO model checking, `raw` instead contains the alphabet, its
intrinsically scoped sentence, and its ranked tree, with the latter two fields
dependent on the alphabet field. There is no arbitrary input encoder and no
uncharged specialized table in either concept statement.

## Runtime quantifiers

The uniform automaton theorem has the order

```text
exists program constant, forall automaton tree wordWidth, ...
```

so the same `Lax808846.Ram.Program` works for every runtime automaton, tree, and
sufficient word width. The fixed-automaton corollary has the distinct order

```text
forall automaton, exists program constant, forall tree wordWidth, ...
```

and intentionally asserts only existential specialization. It does not claim
an effective program-producing function.

The headline MSO theorem has the stronger order

```text
exists program, forall alphabet sentence tree wordWidth, ...
```

Its distinguished input represents the dependent mathematical triple
`(alphabet, sentence over alphabet, tree over alphabet)`. Formula-to-automaton
compilation, when used by the implementation, occurs inside this same RAM
execution and its instruction count is charged. The automaton evaluator is
therefore an internal verified backend rather than the public MSO input
contract. Fixing a sentence yields a separate linear-in-tree-size companion
result; that specialization does not replace the uniform effectiveness claim.

## Proof-package implementation

The proof package may use numeric arena tags, offsets, pointer arithmetic,
temporary arrays, a pure reference evaluator, and IMP+ programs. Conversion
from the distinguished arena to any evaluator-specific working layout must be
verified and charged to the `Lax808846.Ram` instruction count.

The public machine proposition is `Lax808846.RamComputes.ComputesInTime`,
packaged by `Lax560851.RamComplexity.RamComputableWithinUsing`. The public RAM
has dedicated input and output tapes, immutable indexed input, and a counted
terminal instruction. The concrete IMP+ language, compiler, simulation, and
transfer theorem are retained under `Lax759944Proofs.Legacy` as a proof-side
intermediate. They no longer depend on the deleted Lax-865980 package.

`Lax842588Proofs.CheckedRamAdapter` applies the proved instruction embedding
from `Lax759944Proofs.LegacyRamBridge` to each implementation witness. The
embedding preserves the exact supplied input and output lists, working-memory
layout, and word width. It adds at most one instruction for the terminal
charge; increasing the existential time coefficient by one covers that cost.
The public bounds and quantifier order above remain the same.

The input-array marshalling helper is local to
`Lax842588Proofs.ArrayInput`, with attribution to the earlier Lax-62 harness.
There is no Lax-62 dependency. The higher refinement and code-generation
tower is not part of the public concept or runtime claim.

Likely local helpers that may merit later extraction, after the first result
is complete, are semantic/cost/word-bound lemmas for loading and traversing a
distinguished Lax-58 arena. They remain local for now because one application
does not yet establish a stable reusable abstraction.
