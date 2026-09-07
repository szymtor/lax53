import Lax53Proofs.FixedAutomatonModelChecking
import Lax53Proofs.IntrinsicTimeBounds
import Lax53Proofs.IntrinsicSentenceCorrectness

/-! The fixed-sentence headline, with only the certified tree on the input tape. -/

namespace Lax53Proofs.FixedSentenceModelChecking

open Classical Encodable Lax13.Ram Lax13.RamComputes Lax13Proofs.Compile
open Lax52.MSOSyntax Lax53.RankedTree Lax53.TreeStructure Lax53.ValueTranslations
open Lax53.StructuralRepresentations Lax53.MSOLinearTime
open Lax53.TreeModelCheckingEncoding (treeSize maximumRank)
open Lax58.WordArena Lax53Proofs.IntrinsicCompiledTableBounds
open Lax58.RamComplexity

def wordCore (M : EncodedAutomaton) : Nat :=
  2 * encode (encodeAutomaton M) + M.1.length + M.2.1 + M.2.2.1.length +
    maximumRank M.1 + M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + 50

def timeCore (M : EncodedAutomaton) : Nat :=
  FixedTableLoader.timeBound (encodeAutomaton M) + 2000 +
    1000 * (encode (encodeAutomaton M) + 1) ^ 2

theorem time_le (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) :
    FixedAutomatonModelChecking.timeBound M t ≤ timeCore M * (treeSize t + 1) := by
  have htable := bounds_of_code M (encode (encodeAutomaton M)) le_rfl
  have hp := IntrinsicTimeBounds.prepare_time_le M t
  have hb := IntrinsicTimeBounds.backend_time_le M _ htable t
  have hn := AutomatonRamArenaBounds.treeStructure_nodes_add_one M.1 t
  have hm := Lax58Proofs.WordArena.encodeRaw_memoryWords_proof (treeStructure M.1 t)
  have hread : FixedSentencePrepare.timeBound M t ≤
      (FixedTableLoader.timeBound (encodeAutomaton M) + 1000) * (treeSize t + 1) := by
    unfold FixedSentencePrepare.timeBound
    rw [hm]
    nlinarith [Nat.zero_le (FixedTableLoader.timeBound (encodeAutomaton M) * treeSize t)]
  unfold FixedAutomatonModelChecking.timeBound
  calc
    _ ≤ (FixedTableLoader.timeBound (encodeAutomaton M) + 1000) * (treeSize t + 1) +
        (1000 * (treeSize t + 1) +
          1000 * (encode (encodeAutomaton M) + 1) ^ 2 * (treeSize t + 1)) :=
      Nat.add_le_add hread (Nat.add_le_add hp hb)
    _ = _ := by unfold timeCore; ring

theorem exists_fixed_automaton (M : EncodedAutomaton) :
    ∃ (program : Program) (timeCoefficient wordCoefficient : Nat),
      ∀ (t : Tree M.1.toRankedAlphabet) (w : Nat),
      wordCoefficient * (treeStructuralSize M.1 t + treePayloadMax M.1 t + 1) ≤ 2 ^ w →
      ComputesInTime w program {treeInput M.1 t}
        (fun _ => [if M.2.toAutomaton M.1 |>.Accepts t then 1 else 0])
        (fun _ => timeCoefficient * (treeSize t + 1)) := by
  obtain ⟨L, hram⟩ := FixedAutomatonModelChecking.exists_ram M
  let q := L.temps + 2 + L.scalars.length + L.arrays.length + 1
  refine ⟨compileProgram L (FixedAutomatonModelChecking.program M),
    L.const * timeCore M, q * wordCore M, ?_⟩
  intro t w hw
  let S := treeStructuralSize M.1 t
  let N := S + treePayloadMax M.1 t + 1
  let k := wordCore M
  let B := k * N
  have hk : 50 ≤ k := by dsimp [k, wordCore]; omega
  have hN : 0 < N := by dsimp [N]; omega
  have hkB : k ≤ B := Nat.le_mul_of_pos_right _ hN
  have hB : 1 < B := by omega
  have hSN : S < N := by dsimp [N]; omega
  have hn : treeSize t ≤ S := AutomatonRamArenaBounds.treeSize_le_treeStructure_nodes M.1 t
  have hprod : k * S < B := Nat.mul_lt_mul_of_pos_left hSN (by omega)
  have hmem : (encodeRaw (treeStructure M.1 t)).memoryWords < B := by
    rw [Lax58Proofs.WordArena.encodeRaw_memoryWords_proof]
    exact (Nat.mul_le_mul_right S (by omega : 3 ≤ k)).trans_lt hprod
  have hpayload : treePayloadMax M.1 t < B :=
    (show treePayloadMax M.1 t < N by dsimp [N]; omega).trans_le
      (Nat.le_mul_of_pos_left _ (by omega))
  have hvalues : ∀ v ∈ (encodeRaw (treeStructure M.1 t)).toInput, v < B :=
    Lax58Proofs.WordArena.encodeRaw_toInput_lt _ B hpayload (by
      rw [Lax58Proofs.WordArena.encodeRaw_memoryWords_proof] at hmem
      exact Nat.le_of_lt hmem)
  have htable : 2 * encode (encodeAutomaton M) + 3 < B := by
    have : 2 * encode (encodeAutomaton M) + 3 < k := by dsimp [k, wordCore]; omega
    omega
  have ht := bounds_of_code M (encode (encodeAutomaton M)) le_rfl
  have hcode : encode (encodeAutomaton M) < B := by omega
  have hstates : treeSize t * M.2.2.1.length < B := by
    have hT : M.2.2.1.length ≤ k := by dsimp [k, wordCore]; omega
    have hh := Nat.mul_le_mul hn hT
    exact (hh.trans_eq (Nat.mul_comm S k)).trans_lt hprod
  have hplus : k + treeSize t ≤ B := by
    have hh := Nat.mul_le_mul_left k (by omega : treeSize t + 1 ≤ N)
    have hn' : treeSize t ≤ k * treeSize t := Nat.le_mul_of_pos_left _ (by omega)
    dsimp [B]
    nlinarith
  have hwork : M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
      M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + treeSize t + 20 < B := by
    have hh : M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
        M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + 20 < k := by
      dsimp [k, wordCore]; omega
    omega
  have hw' : q * B ≤ 2 ^ w := by simpa only [B, k, N, S, Nat.mul_assoc] using hw
  have hfit : L.FitsWords B w := by
    refine ⟨hB, ?_, ?_⟩
    · dsimp [q] at hw'
      nlinarith
    · unfold Layout.span
      dsimp [q] at hw'
      nlinarith [Nat.mul_le_mul_left (L.temps + 2 + L.scalars.length) (Nat.le_of_lt hB)]
  have hexec := hram B w t hfit htable hmem hvalues
    (fun v hv => (ht.values v hv).trans_lt hcode) (ht.length.trans_lt hcode) hstates hwork
  have htime : L.const * FixedAutomatonModelChecking.timeBound M t ≤
      (L.const * timeCore M) * (treeSize t + 1) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left L.const (time_le M t)
  intro x hx
  obtain ⟨steps, hs, hr⟩ := hexec x hx
  exact ⟨steps, hs.trans htime, hr⟩

/-- Expanded fixed-sentence theorem retained behind the concise reusable
RAM-complexity statement. -/
theorem exists_fixed_sentence_modelChecking_expanded
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    ∃ (program : Program) (timeCoefficient wordCoefficient : Nat),
      ∀ (t : Tree alphabet.toRankedAlphabet) (w : Nat),
      TreePayloadsFitInWord alphabet t w →
      3 * treeStructuralSize alphabet t ≤ 2 ^ w →
      wordCoefficient * (treeStructuralSize alphabet t + treePayloadMax alphabet t + 1) ≤ 2 ^ w →
      ComputesInTime w program {treeInput alphabet t}
        (fun _ => if t ∈ sentenceLanguage phi then [1] else [0])
        (fun _ => timeCoefficient * (treeSize t + 1)) := by
  obtain ⟨p, ct, cw, h⟩ := exists_fixed_automaton (IntrinsicModelChecking.compiled alphabet phi)
  refine ⟨p, ct, cw, fun t w _ _ hw => ?_⟩
  have hh := h t w hw
  simpa only [IntrinsicModelChecking.compiled, IntrinsicSentenceCorrectness.compileRows_sentence,
    apply_ite (fun v : Nat => [v])] using hh

/--
---
conclusion: Lax53.MSOLinearTime.exists_fixed_sentence_modelChecking
---
Specialize the pure automaton before program choice, then materialize it
within a counted tree-only run from zero memory. The reusable predicate
packages the program and all sufficient-width premises.
-/
theorem exists_fixed_sentence_modelChecking_proof
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) :
    ∃ timeCoefficient wordCoefficient : Nat,
      RamComputableWithinUsing (treePresentation alphabet) natOutput
        (fun t => if t ∈ sentenceLanguage phi then 1 else 0)
        (fun t => timeCoefficient * (treeSize t + 1))
        (fun t => wordCoefficient * inputMagnitudeUsing
          (treePresentation alphabet) t) := by
  obtain ⟨program, timeCoefficient, wordCoefficient, h⟩ :=
    exists_fixed_sentence_modelChecking_expanded alphabet phi
  refine ⟨timeCoefficient, wordCoefficient, program, ?_⟩
  intro t w hpayload harena hword
  by_cases hsatisfies : t ∈ sentenceLanguage phi <;>
    simpa [treePresentation, treeInput, inputMagnitudeUsing, natOutput,
      Lax58.WordArena.encode, Lax58.StructuralPresentation.presentationOf,
      hsatisfies] using h t w hpayload harena hword

end Lax53Proofs.FixedSentenceModelChecking
