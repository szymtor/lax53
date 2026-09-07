import Lax53Proofs.AutomatonRamEvaluateBody

namespace Lax53Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 2000000
open Classical

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning
open Lax53.ValueTranslations
open Lax53.TreeModelCheckingEncoding
open Lax53Proofs.AutomatonRamProgram
open Lax53Proofs.EncodedAutomatonWordEvaluation

theorem pushSymbol_length_le_succ (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (stack : List CodeString) (symbol : Nat) :
    (pushSymbol alphabet M stack symbol).length ≤ stack.length + 1 := by
  simp [pushSymbol]

theorem nodeStates_length (M : EncodedAutomaton) (states : List Nat)
    (stack : List CodeString) (symbol : Nat) :
    (nodeStates M states stack symbol).length = states.length := by
  simp [nodeStates, writePrefix_length]

theorem nodeLengths_length (M : EncodedAutomaton) (lengths : List Nat)
    (stack : List CodeString) (symbol : Nat) :
    (nodeLengths M lengths stack symbol).length = lengths.length := by
  simp [nodeLengths]

theorem nodeStates_values_lt (B : Nat) (M : EncodedAutomaton)
    (states : List Nat) (stack : List CodeString) (symbol : Nat)
    (h0 : 0 < B) (hstates : ∀ v ∈ states, v < B) (hQ : M.2.1 < B) :
    ∀ v ∈ nodeStates M states stack symbol, v < B := by
  apply writePrefix_values_lt h0 hstates
  intro q hq
  exact lt_trans (mem_parentStates_lt M.2 symbol q _ hq) hQ

theorem nodeLengths_values_lt (B : Nat) (M : EncodedAutomaton)
    (lengths : List Nat) (stack : List CodeString) (symbol : Nat)
    (hlengths : ∀ v ∈ lengths, v < B) (hT : M.2.2.1.length < B) :
    ∀ v ∈ nodeLengths M lengths stack symbol, v < B := by
  apply set_values_lt hlengths
  exact lt_of_le_of_lt (parentStates_length_le M.2 symbol _) hT

/-- A deliberately loose absolute coefficient paying for one node plus one
unit of rank. Its quadratic dependence is on the transition count. -/
def nodeCoefficient (M : EncodedAutomaton) : Nat :=
  300 * (M.2.2.1.length + 1) ^ 2

theorem nodeBodyCost_le (M : EncodedAutomaton) (k : Nat) :
    4 + (nodeCoreCost M k + 20) ≤ nodeCoefficient M * (k + 1) := by
  unfold nodeCoreCost transitionScanCost nodeCoefficient
  nlinarith [Nat.zero_le M.2.2.1.length, Nat.zero_le k]

def EvalPotential (M : EncodedAutomaton) (sigma : Env) : Nat :=
  nodeCoefficient M * (sigma.vars "n" - sigma.vars "node" +
    rankSum M.1 ((sigma.arrs "W").drop (sigma.vars "node")))

/-- The loop state is a split of the original word into a processed prefix
and the unread suffix, together with the represented semantic stack. -/
def EvalLoopInv (B : Nat) (M : EncodedAutomaton) (word : CodeString)
    (sigma : Env) : Prop :=
  ∃ processed remaining stack states lengths,
    word = processed ++ remaining ∧
      sigma.vars "node" = processed.length ∧ sigma.arrs "W" = word ∧
      EvalFields M word.length sigma ∧
      EvalStorage M states lengths stack sigma ∧
      stack = evalWord M.1 M.2 processed ∧
      SafeEval M.1 M.2 remaining stack ∧
      stack.length ≤ processed.length ∧
      states.length = word.length * M.2.2.1.length ∧
      lengths.length = word.length ∧
      (∀ v ∈ states, v < B) ∧ (∀ v ∈ lengths, v < B)

theorem evaluateTreeLoop_spec (B : Nat) (M : EncodedAutomaton)
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
      (maximumRank M.1 + 3) < B) :
    Spec B (EvalLoopInv B M word) evaluateTreeLoop
      (fun _ sigma' => EvalLoopInv B M word sigma' ∧
        sigma'.vars "node" = word.length)
      (nodeCoefficient M * (word.length + rankSum M.1 word) + 4) := by
  have hloop : Spec B (EvalLoopInv B M word) evaluateTreeLoop
      (fun _ sigma' => EvalLoopInv B M word sigma' ∧
        (Cond.lt (.var "node") (.var "n")).evalB B sigma' = some false)
      (nodeCoefficient M * (word.length + rankSum M.1 word) + 4) := by
    unfold evaluateTreeLoop
    apply Spec.while_potential (EvalLoopInv B M word) (EvalPotential M)
    · intro sigma hinv
      rcases hinv with ⟨processed, remaining, stack, states, lengths,
        hword, hnode, hW, hfields, hstorage, hstack, hsafe, hstackLen,
        hstatesLen, hlengthsLen, hstatesB, hlengthsB⟩
      refine ⟨decide (processed.length < word.length), ?_⟩
      rcases hfields with ⟨_, _, _, _, _, _, _, _, _, hn⟩
      have hpB : processed.length < B := by
        have hlen := congrArg List.length hword
        simp at hlen
        omega
      simp [hnode, hn, hwordLenB, hpB]
    · intro sigma hinv hcond
      rcases hinv with ⟨processed, remaining, stack, states, lengths,
        hword, hnode, hW, hfields, hstorage, hstack, hsafe, hstackLen,
        hstatesLen, hlengthsLen, hstatesB, hlengthsB⟩
      have hprocessed : processed.length < word.length := by
        rcases hfields with ⟨_, _, _, _, _, _, _, _, _, hn⟩
        have hc : processed.length < B ∧ processed.length < word.length := by
          simpa [hnode, hn, hwordLenB] using hcond
        exact hc.2
      have hremaining : remaining ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hword
        rw [hnil] at hlen
        simp at hlen
        omega
      obtain ⟨symbol, rest, hremainingEq⟩ := List.exists_cons_of_ne_nil hremaining
      subst remaining
      rcases hsafe with ⟨hsafeHead, hsafeRest⟩
      have hsymbolMem : symbol ∈ word := by
        rw [hword]
        simp
      have hsymbolIndex := hsymbols symbol hsymbolMem
      have hsymbolB : symbol < B := lt_trans hsymbolIndex (by
        have hA : M.1.length < B := by
          have := hworkB
          omega
        exact hA)
      rcases hstorage with ⟨hS, hL, hO, hdepth, hrep⟩
      have hstatesLenB : states.length < B := by
        rw [hstatesLen]
        exact hstatesCapacityB
      have hstackRoom : stack.length < lengths.length := by
        rw [hlengthsLen]
        omega
      have hcapacity : states.length = lengths.length * M.2.2.1.length := by
        rw [hstatesLen, hlengthsLen]
      have hsymbolGet : word.getD processed.length 0 = symbol := by
        rw [hword]
        simp
      have hbody := evaluateTreeBody_spec B M word.length processed.length
        states lengths stack word symbol h0 h1 hparameterB hstatesB hlengthsB
        hparameterLenB hstatesLenB (by omega) hsymbolIndex hstackRoom hcapacity
        hwidthB hQB hTB hsymbolB hworkB hsafeHead hrep (by omega) (by omega)
      have hpre : NodeBodyContext M word.length processed.length states lengths
          stack word symbol sigma := by
        exact ⟨hfields, ⟨hS, hL, hO, hdepth, hrep⟩, hW, hsymbolGet, hnode⟩
      obtain ⟨sigma', hrun, hresult⟩ := hbody.run hpre
      rcases hresult with ⟨hfields', hstorage', hW', hnode'⟩
      let states' := nodeStates M states stack symbol
      let lengths' := nodeLengths M lengths stack symbol
      let stack' := pushSymbol M.1 M.2 stack symbol
      have hstatesB' : ∀ v ∈ states', v < B :=
        nodeStates_values_lt B M states stack symbol h0 hstatesB hQB
      have hlengthsB' : ∀ v ∈ lengths', v < B :=
        nodeLengths_values_lt B M lengths stack symbol hlengthsB hTB
      have hstack' : stack' = evalWord M.1 M.2 (processed ++ [symbol]) := by
        rw [evalWord_append, ← hstack]
        rfl
      have hword' : word = (processed ++ [symbol]) ++ rest := by
        simpa [List.append_assoc] using hword
      have hinv' : EvalLoopInv B M word sigma' := by
        refine ⟨processed ++ [symbol], rest, stack', states', lengths', hword',
          ?_, hW', hfields', ?_, hstack', hsafeRest, ?_, ?_, ?_,
          hstatesB', hlengthsB'⟩
        · simpa using hnode'
        · simpa [states', lengths', stack'] using hstorage'
        · calc
            stack'.length ≤ stack.length + 1 :=
              pushSymbol_length_le_succ M.1 M.2 stack symbol
            _ ≤ (processed ++ [symbol]).length := by simp; omega
        · simpa [states', nodeStates_length] using hstatesLen
        · simpa [lengths', nodeLengths_length] using hlengthsLen
      refine ⟨sigma', nodeCoreCost M (M.1.getD symbol 0) + 20, hrun,
        hinv', ?_⟩
      have hcharge := nodeBodyCost_le M (M.1.getD symbol 0)
      have hpotential : EvalPotential M sigma =
          nodeCoefficient M * (M.1.getD symbol 0 + 1) +
            EvalPotential M sigma' := by
        rw [EvalPotential, EvalPotential, hW, hW']
        rcases hfields with ⟨_, _, _, _, _, _, _, _, _, hn⟩
        rcases hfields' with ⟨_, _, _, _, _, _, _, _, _, hn'⟩
        rw [hn, hn', hnode, hnode']
        rw [hword]
        simp [rankSum, Nat.add_sub_add_left]
        ring
      change 4 + (nodeCoreCost M (M.1.getD symbol 0) + 20) +
        EvalPotential M sigma' ≤ EvalPotential M sigma
      omega
    · intro sigma hinv
      exact hinv
    · intro sigma hinv
      rcases hinv with ⟨processed, remaining, stack, states, lengths,
        hword, hnode, hW, hfields, hstorage, hstack, hsafe, hstackLen,
        hstatesLen, hlengthsLen, hstatesB, hlengthsB⟩
      rw [EvalPotential, hW]
      rcases hfields with ⟨_, _, _, _, _, _, _, _, _, hn⟩
      rw [hn, hnode, hword]
      simp only [List.drop_left, List.length_append, Nat.add_sub_cancel_left]
      have hmeasure : remaining.length + rankSum M.1 remaining ≤
          word.length + rankSum M.1 word := by
        rw [hword, rankSum_append]
        simp
        omega
      have hcharged := Nat.add_le_add_right
        (Nat.mul_le_mul_left (nodeCoefficient M) hmeasure) 4
      simpa [hword] using hcharged
  exact hloop.post (by
    intro sigma sigma' hinv ⟨hinv', hfalse⟩
    have hinvCopy := hinv'
    rcases hinv' with ⟨processed, remaining, stack, states, lengths,
      hword, hnode, hW, hfields, hstorage, hstack, hsafe, hstackLen,
      hstatesLen, hlengthsLen, hstatesB, hlengthsB⟩
    rcases hfields with ⟨_, _, _, _, _, _, _, _, _, hn⟩
    have hfalse' : processed.length < B ∧ word.length ≤ processed.length := by
      simpa [hnode, hn, hwordLenB] using hfalse
    have hlen := congrArg List.length hword
    simp at hlen
    exact ⟨hinvCopy, by omega⟩)

end Lax53Proofs.AutomatonRamCorrectness
