import Lax53.TreeModelCheckingEncoding

namespace Lax53Proofs.TreeModelCheckingEncoding

open Lax53.TreeModelCheckingEncoding
open Lax58.WordArena

/--
---
conclusion: Lax53.TreeModelCheckingEncoding.automatonInput_length
---
-/
theorem automatonInput_length_proof (M : Lax53.ValueTranslations.EncodedAutomaton)
    (t : Lax53.RankedTree.Tree M.1.toRankedAlphabet) :
    (automatonInput M t).length = 3 * inputStructuralSize M t + 1 := by
  exact encodeRaw_toInput_length (automatonTreeRaw M t)

end Lax53Proofs.TreeModelCheckingEncoding
