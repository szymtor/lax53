We formalize bottom-up tree automata on finite ranked trees, together with the
trees' relational presentation by unary label predicates and indexed child
relations. The automata in our main results have finitely many states. We
prove determinization and the equivalence between recognizable ranked-tree
languages and languages definable in monadic second-order logic, using the MSO
syntax and semantics of `lax-52`. This formalizes the characterization proved
by Thatcher and Wright (1968) and, independently, by Doner (1970). We
additionally give value-level translations in both directions,
preserving the ranked alphabet and represented tree language. Using `lax-58`,
we certify explicit constructor-structural presentations of the finite
automaton data and ranked trees, without introducing a second public formula
syntax or exposing low-level arena details in the mathematical translations.
Finally, we state word-RAM model checking at two levels. Automaton acceptance
is linear in the number of tree nodes with quadratic dependence on the
certified structural automaton size. The stronger MSO statement chooses one
program before the runtime alphabet, intrinsic sentence, and tree, and charges
formula compilation as part of its execution. Both use distinguished
`lax-58` arena inputs and its reusable word-RAM complexity predicate, which
packages the common sufficient-word-width premises while bounding actual
`lax-808846` instructions. An ordinary proof-package corollary fixes the
alphabet and sentence before program choice, receives only the tree, and is
linear in the tree size with a sentence-dependent coefficient. The public
runtime statements are the two uniform results.

This is a Lean 4.33 port of [the original Lean 4.30 draft](https://laxarchive.org/lax-53/).
