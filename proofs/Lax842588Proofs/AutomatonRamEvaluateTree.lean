import Lax842588Proofs.AutomatonRamEvaluateLoop

namespace Lax842588Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1500000
open Classical

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamProgram
open Lax842588Proofs.EncodedAutomatonWordEvaluation

theorem encodeTree_symbols_lt (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ∀ symbol ∈ encodeTree alphabet t, symbol < alphabet.length := by
  induction t with
  | node a children ih =>
      intro symbol hsymbol
      simp only [encodeTree, List.mem_append, List.mem_singleton] at hsymbol
      rcases hsymbol with hchildren | rfl
      · rw [List.mem_flatten] at hchildren
        obtain ⟨childWord, hchildWord, hsymbolChild⟩ := hchildren
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hchildWord
        subst childWord
        exact ih i symbol hsymbolChild
      · exact a.isLt

theorem treeSize_pos (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) : 0 < treeSize t := by
  cases t with
  | node a children =>
      simp [treeSize, encodeTree]

def EvaluateTreeContext (B : Nat) (M : EncodedAutomaton) (word : CodeString)
    (sigma : Env) : Prop :=
  EvalFields M word.length sigma ∧ sigma.arrs "W" = word ∧
    sigma.arrs "S" = List.replicate (word.length * M.2.2.1.length) 0 ∧
    sigma.arrs "L" = List.replicate word.length 0 ∧
    (sigma.arrs "O").length = M.2.2.1.length ∧
    (sigma.arrs "W").length * M.2.2.1.length < B

theorem evalLoopInv_init (B : Nat) (M : EncodedAutomaton) (word : CodeString)
    (sigma : Env) (h0 : 0 < B) (hsafe : SafeEval M.1 M.2 word [])
    (hctx : EvaluateTreeContext B M word sigma) :
    EvalLoopInv B M word ((sigma.setVar "node" 0).setVar "depth" 0) := by
  rcases hctx with ⟨hfields, hW, hS, hL, hO, hcapacity⟩
  refine ⟨[], word, [],
    List.replicate (word.length * M.2.2.1.length) 0,
    List.replicate word.length 0, by simp, by simp, ?_, ?_, ?_, by simp [evalWord],
    hsafe, by simp, by simp, by simp, ?_, ?_⟩
  · simpa using hW
  · simpa [EvalFields] using hfields
  · simp [EvalStorage, RowsRep, hS, hL, hO]
  · intro v hv
    simp only [List.mem_replicate] at hv
    rcases hv with ⟨-, rfl⟩
    exact h0
  · intro v hv
    simp only [List.mem_replicate] at hv
    rcases hv with ⟨-, rfl⟩
    exact h0

theorem evaluateTree_spec (B : Nat) (M : EncodedAutomaton)
    (word : CodeString)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hwordLenB : word.length < B)
    (hstatesCapacityB : word.length * M.2.2.1.length < B)
    (hsymbols : ∀ symbol ∈ word, symbol < M.1.length)
    (hwidthB : maximumRank M.1 + 3 < B) (hQB : M.2.1 < B)
    (hTB : M.2.2.1.length < B)
    (hworkB : M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) < B)
    (hsafe : SafeEval M.1 M.2 word []) :
    Spec B (EvaluateTreeContext B M word) evaluateTree
      (fun _ sigma' => EvalLoopInv B M word sigma' ∧
        sigma'.vars "node" = word.length)
      (nodeCoefficient M * (word.length + rankSum M.1 word) + 20) := by
  have hloop := evaluateTreeLoop_spec B M word h0 h1 hparameterB
    hparameterLenB hwordLenB hstatesCapacityB hsymbols hwidthB hQB hTB hworkB
  unfold evaluateTree seqs
  run_vcg [hloop]
  all_goals try assumption
  all_goals try apply evalLoopInv_init B M word <;> assumption
  all_goals simp_all [EvaluateTreeContext, EvalLoopInv, EvalFields, EvalStorage,
    RowsRep, evalWord]
  all_goals try exact hsafe
  all_goals try
    have hWlen : (σ.arrs "W").length = word.length := by aesop
    rw [hWlen]
    exact hstatesCapacityB
  all_goals try aesop
  all_goals omega

end Lax842588Proofs.AutomatonRamCorrectness
