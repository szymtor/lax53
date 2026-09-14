import Lax842588Proofs.IntrinsicParameterEncoding
import Lax842588Proofs.IntrinsicModelChecking

/-!
Parameter-only bounds on the compiled table and its evaluator dimensions.
The auxiliary pure code is used only to prove a numerical envelope; execution
is still the complete counted public-input program already constructed.
-/

namespace Lax842588Proofs.IntrinsicCompiledTableBounds

open Encodable Lax146103.MSOSyntax Lax842588.ValueTranslations Lax842588.TreeStructure
open Lax842588.MSOLinearTime Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.IntrinsicParameterEncoding Lax842588Proofs.PrimitiveRecursiveBounds
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicModelChecking
open Lax842588Proofs.AutomatonTableEncoding

structure TableBounds (M : EncodedAutomaton) (H : Nat) : Prop where
  length : (encodeAutomaton M).length ≤ H
  values : ∀ v ∈ encodeAutomaton M, v ≤ H
  states : M.2.1 ≤ H
  transitions : M.2.2.1.length ≤ H
  accepting : M.2.2.2.length ≤ H

theorem bounds_of_code (M : EncodedAutomaton) (H : Nat)
    (hcode : encode (encodeAutomaton M) ≤ H) : TableBounds M H := by
  have hvalues : ∀ v ∈ encodeAutomaton M, v ≤ H := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    exact (CompilerArrayPacking.entry_le_encode _ i hi).trans hcode
  have hget (i : Nat) : (encodeAutomaton M).getD i 0 ≤ H := by
    have hh : (encodeAutomaton M).getD i 0 < H + 1 :=
      AutomatonRamCorrectness.getD_lt_of_mem_bound (by omega)
        (fun v hv => Nat.lt_succ_of_le (hvalues v hv))
    omega
  refine ⟨(length_le_encode _).trans hcode, hvalues, ?_, ?_, ?_⟩
  · simpa only [encodeAutomaton_Q] using hget (M.1.length + 1)
  · simpa only [encodeAutomaton_T] using hget (M.1.length + 2)
  · simpa only [encodeAutomaton_acceptCount] using
      hget (M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3))

def tableAllowance (d : Code) (p : Nat) : Nat := budget d (inputCodeBound p)

theorem tableAllowance_prim (d : Code) : Primrec (tableAllowance d) :=
  (budget_prim d).comp inputCodeBound_prim

theorem exists_table_bound : ∃ d : Code, ∀ (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet)),
    TableBounds (compiled alphabet φ) (tableAllowance d (parameterSize alphabet φ)) := by
  obtain ⟨d, hd⟩ := exists_typed_code compileTable_prim
  refine ⟨d, fun alphabet φ => ?_⟩
  apply bounds_of_code
  have heval := eval_le_budget d (inputCodeBound (parameterSize alphabet φ))
    (encode (alphabet, (postorder alphabet φ).map fields)) (input_code_le alphabet φ)
  rw [typed_code_on_value hd, encode_some] at heval
  exact (Nat.le_succ _).trans heval

end Lax842588Proofs.IntrinsicCompiledTableBounds
