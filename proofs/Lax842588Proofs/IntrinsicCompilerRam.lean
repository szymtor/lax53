import Lax842588Proofs.IntrinsicCompilerComputability
import Lax842588Proofs.PrimitiveRecursiveRam

/-!
RAM execution of the complete intrinsic formula compiler on its normalized
internal input. Arena extraction and output-table materialization remain
separate charged obligations; no theorem here treats the normalized scalar
as the public model-checking input.
-/

namespace Lax842588Proofs.IntrinsicCompilerFields

open Lax759944Proofs.Legacy.Ram Lax759944Proofs.Legacy.RamComputes
open Lax146103.MSOSyntax Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicFormulaCompiler
open Lax842588Proofs.PrimitiveRecursiveRam

theorem compileRows_ram :
    ∃ (p : Program) (time words : Nat → Nat), Primrec time ∧ Primrec words ∧
      ∀ (alphabet : RankedAlphabetCode) (rows : List (List Nat)) (w : Nat),
        words (Encodable.encode (alphabet, rows)) ≤ 2 ^ w →
        ComputesInTime w p {[Encodable.encode (alphabet, rows)]}
          (fun _ => [Encodable.encode (some (compileRows alphabet rows))])
          (fun _ => time (Encodable.encode (alphabet, rows))) := by
  obtain ⟨p, time, words, ht, hw, hrun⟩ := exists_typed_ram compileRows_prim
  exact ⟨p, time, words, ht, hw, fun alphabet rows w hfit => hrun (alphabet, rows) w hfit⟩

/-- One fixed RAM program handles every intrinsic formula once its genuine
postorder fields have been constructed in the internal numeric convention.
All automaton construction and closure operations execute within this run. -/
theorem intrinsicCompiler_ram :
    ∃ (p : Program) (time words : Nat → Nat), Computable time ∧ Computable words ∧
      ∀ (alphabet : RankedAlphabetCode) (n m : Nat)
        (f : Formula (treeSignature alphabet.toRankedAlphabet) n m) (w : Nat),
        words (Encodable.encode (alphabet, (postorder alphabet f).map fields)) ≤ 2 ^ w →
        ComputesInTime w p {[Encodable.encode (alphabet, (postorder alphabet f).map fields)]}
          (fun _ => [Encodable.encode (some (compileFormula alphabet f))])
          (fun _ => time (Encodable.encode (alphabet, (postorder alphabet f).map fields))) := by
  obtain ⟨p, time, words, ht, hw, hrun⟩ := compileRows_ram
  refine ⟨p, time, words, ht.to_comp, hw.to_comp, ?_⟩
  intro alphabet n m f w hfit
  simpa only [compileRows_eq] using hrun alphabet ((postorder alphabet f).map fields) w hfit

end Lax842588Proofs.IntrinsicCompilerFields
