We formalize finite ranked trees, their relational presentation by unary label
predicates and indexed child relations, and bottom-up finite tree automata. We
prove determinization and the equivalence between recognizable ranked-tree
languages and languages definable in monadic second-order logic, using the MSO
syntax and semantics of `lax-52`. This formalizes the characterization proved
by Thatcher and Wright (1968) and, independently, by Doner (1970). We
additionally give uniform value-level translations in both directions,
preserving the ranked alphabet and represented tree language. Using `lax-58`,
we certify explicit constructor-structural presentations of the finite
automaton data, raw formulas, and ranked trees, without exposing low-level
arena details in the mathematical translations. Finally, we formalize
word-RAM model checking: automaton acceptance is linear in the number of tree
nodes with quadratic dependence on the encoded automaton size. Precompilation
of a sentence fixed outside the measured execution yields linear-time MSO
model checking with a sentence-dependent coefficient.
