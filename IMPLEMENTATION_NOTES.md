# Structural RAM implementation notes

This note records the implementation boundary for the coordinated Lax-58 and
Lax-53 revision. It is not a concept module.

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

so the same Lax-13 program works for every runtime automaton, tree, and
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
verified and charged to the Lax-13 instruction count.

At the currently registered revisions, `Lax865980.RamComputes` supplies the public
machine proposition, while the concrete IMP+ language, compiler, simulation,
and transfer theorem remain in `Lax865980Proofs`. The verified input-array
marshalling helper used by the existing evaluator, `Codegen.Harness`, moved to
Lax-62 together with the higher refinement/autoref/code-generation tower.
Lax-53 therefore has a proof-only Lax-62 dependency for that helper; the
remaining higher-level tower is not part of the public concept or runtime
claim.

Likely local helpers that may merit later extraction, after the first result
is complete, are semantic/cost/word-bound lemmas for loading and traversing a
distinguished Lax-58 arena. They remain local for now because one application
does not yet establish a stable reusable abstraction.
