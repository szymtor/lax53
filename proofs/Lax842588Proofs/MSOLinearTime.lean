import Lax842588.MSOLinearTime
import Lax560851Proofs.WordArena

namespace Lax842588Proofs.MSOLinearTime

open Lax146103.MSOSyntax
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.MSOLinearTime
open Lax560851.WordArena

/--
---
conclusion: Lax842588.MSOLinearTime.modelCheckingInput_length
---
The exact input footprint is inherited from the distinguished Lax-58 arena;
no formula serialization layer intervenes.
-/
theorem modelCheckingInput_length_proof (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    (modelCheckingInput alphabet phi t).length =
      3 * inputStructuralSize alphabet phi t + 1 := by
  simpa [modelCheckingInput, inputStructuralSize] using
    encodeRaw_toInput_length (msoTreeRaw alphabet phi t)

end Lax842588Proofs.MSOLinearTime
