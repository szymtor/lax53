import Lax53.MSOLinearTime
import Lax58Proofs.WordArena

namespace Lax53Proofs.MSOLinearTime

open Lax52.MSOSyntax
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53.ValueTranslations
open Lax53.MSOLinearTime
open Lax58.WordArena

/--
---
conclusion: Lax53.MSOLinearTime.modelCheckingInput_length
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

end Lax53Proofs.MSOLinearTime
