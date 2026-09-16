import Lax842588.TreeModelCheckingEncoding

namespace Lax842588Proofs.TreeModelCheckingEncoding

open Lax842588.TreeModelCheckingEncoding
open Lax560851.WordArena

/-- Supporting representation lemma. -/
theorem automatonInput_length_proof (M : Lax842588.ValueTranslations.EncodedAutomaton)
    (t : Lax842588.RankedTree.Tree M.1.toRankedAlphabet) :
    (automatonInput M t).length = 3 * inputStructuralSize M t + 1 := by
  exact encodeRaw_toInput_length (automatonTreeRaw M t)

end Lax842588Proofs.TreeModelCheckingEncoding
