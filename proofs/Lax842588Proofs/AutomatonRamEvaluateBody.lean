import Lax842588Proofs.AutomatonRamNodeSpec

namespace Lax842588Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamProgram
open Lax842588Proofs.AutomatonTableEncoding
open Lax842588Proofs.EncodedAutomatonWordEvaluation

/-- Header fields which remain fixed while the postorder tree word is read. -/
def EvalFields (M : EncodedAutomaton) (treeLength : Nat) (sigma : Env) : Prop :=
  sigma.arrs "P" = encodeAutomaton M ∧
    sigma.vars "A" = M.1.length ∧ sigma.vars "Q" = M.2.1 ∧
    sigma.vars "T" = M.2.2.1.length ∧
    sigma.vars "R" = maximumRank M.1 ∧
    sigma.vars "width" = maximumRank M.1 + 3 ∧
    sigma.vars "records" = M.1.length + 4 ∧
    sigma.vars "acceptBase" =
      M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) ∧
    sigma.vars "F" = M.2.2.2.length ∧ sigma.vars "n" = treeLength

/-- Concrete arrays representing the abstract reachable-state stack. -/
def EvalStorage (M : EncodedAutomaton) (states lengths : List Nat)
    (stack : List CodeString) (sigma : Env) : Prop :=
  sigma.arrs "S" = states ∧ sigma.arrs "L" = lengths ∧
    (sigma.arrs "O").length = M.2.2.1.length ∧
    sigma.vars "depth" = stack.length ∧
    RowsRep states lengths M.2.2.1.length stack.reverse

def NodeBodyContext (M : EncodedAutomaton) (treeLength node : Nat)
    (states lengths : List Nat) (stack : List CodeString)
    (word : CodeString) (symbol : Nat) (sigma : Env) : Prop :=
  EvalFields M treeLength sigma ∧ EvalStorage M states lengths stack sigma ∧
    sigma.arrs "W" = word ∧ word.getD node 0 = symbol ∧
    sigma.vars "node" = node

def NodeBodyResult (M : EncodedAutomaton) (treeLength node : Nat)
    (states lengths : List Nat) (stack : List CodeString)
    (word : CodeString) (symbol : Nat) (sigma : Env) : Prop :=
  EvalFields M treeLength sigma ∧
    EvalStorage M (nodeStates M states stack symbol)
      (nodeLengths M lengths stack symbol)
      (pushSymbol M.1 M.2 stack symbol) sigma ∧
    sigma.arrs "W" = word ∧ sigma.vars "node" = node + 1

/-- One iteration of the postorder evaluator implements `pushSymbol`. -/
theorem evaluateTreeBody_spec (B : Nat) (M : EncodedAutomaton)
    (treeLength node : Nat) (states lengths : List Nat)
    (stack : List CodeString) (word : CodeString) (symbol : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (hparameterB : ∀ v ∈ encodeAutomaton M, v < B)
    (hstatesB : ∀ v ∈ states, v < B)
    (hlengthsB : ∀ v ∈ lengths, v < B)
    (hparameterLenB : (encodeAutomaton M).length < B)
    (hstatesLenB : states.length < B) (hlengthsLenB : lengths.length < B)
    (hsymbolIndex : symbol < M.1.length)
    (hstackRoom : stack.length < lengths.length)
    (hcapacity : states.length = lengths.length * M.2.2.1.length)
    (hwidthB : maximumRank M.1 + 3 < B) (hQB : M.2.1 < B)
    (hTB : M.2.2.1.length < B) (hsymbolB : symbol < B)
    (hworkB : M.1.length + 4 + M.2.2.1.length * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) < B)
    (hsafe : M.1.getD symbol 0 ≤ stack.length)
    (hrep : RowsRep states lengths M.2.2.1.length stack.reverse)
    (hnodeB : node + 1 < B) (hnodeWord : node < word.length) :
    Spec B (NodeBodyContext M treeLength node states lengths stack word symbol)
      evaluateTreeBody
      (fun _ sigma' =>
        NodeBodyResult M treeLength node states lengths stack word symbol sigma')
      (nodeCoreCost M (M.1.getD symbol 0) + 20) := by
  have hsymbolAddr : symbol + 1 < (encodeAutomaton M).length := by
    rw [encodeAutomaton_length]
    omega
  have hsymbolRead : (encodeAutomaton M)[symbol + 1]?.getD 0 =
      M.1.getD symbol 0 := by
    rw [← List.getD_eq_getElem?_getD]
    exact encodeAutomaton_rank M symbol hsymbolIndex
  have hkB : M.1.getD symbol 0 < B := by
    have h := getD_lt_of_mem_bound (i := symbol + 1) h0 hparameterB
    rw [encodeAutomaton_rank M symbol hsymbolIndex] at h
    exact h
  have hcore := scanInstall_spec B M states lengths stack symbol h0 h1
    hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB hlengthsLenB
    hsymbolIndex hstackRoom hcapacity hwidthB hQB hTB hsymbolB hworkB hsafe hrep
  have hcoreF : Spec B
      (fun sigma => ScanInstallContext M states lengths stack symbol sigma ∧
        EvalFields M treeLength sigma ∧ sigma.arrs "W" = word ∧
        sigma.vars "node" = node)
      (.seq scanTransitions installParent)
      (fun _ sigma' =>
        EvalFields M treeLength sigma' ∧
          EvalStorage M (nodeStates M states stack symbol)
            (nodeLengths M lengths stack symbol)
            (pushSymbol M.1 M.2 stack symbol) sigma' ∧
          sigma'.arrs "W" = word ∧ sigma'.vars "node" = node)
      (nodeCoreCost M (M.1.getD symbol 0)) := by
    refine hcore.frame.conseq (fun _ h => h.1) ?_ le_rfl
    rintro sigma sigma' hpre ⟨hresult, hvars, harrs, hinp, hout⟩
    rcases hpre with ⟨hscan, hfields, hW0, hnode0⟩
    rcases hfields with ⟨hP, hA, hQ, hT, hR, hwidth, hrecords,
      hacceptBase, hF, hn⟩
    have hfields' : EvalFields M treeLength sigma' :=
      ⟨(harrs "P" (by decide)).trans hP,
        (hvars "A" (by decide)).trans hA,
        (hvars "Q" (by decide)).trans hQ,
        (hvars "T" (by decide)).trans hT,
        (hvars "R" (by decide)).trans hR,
        (hvars "width" (by decide)).trans hwidth,
        (hvars "records" (by decide)).trans hrecords,
        (hvars "acceptBase" (by decide)).trans hacceptBase,
        (hvars "F" (by decide)).trans hF,
        (hvars "n" (by decide)).trans hn⟩
    rcases hresult with ⟨hS, hL, hO, hdepth, hrep'⟩
    have hstorage' : EvalStorage M (nodeStates M states stack symbol)
        (nodeLengths M lengths stack symbol)
        (pushSymbol M.1 M.2 stack symbol) sigma' := by
      rw [hS, hL] at hrep'
      exact ⟨hS, hL, hO, hdepth, hrep'⟩
    exact ⟨hfields', hstorage',
      (harrs "W" (by decide)).trans hW0,
      (hvars "node" (by decide)).trans hnode0⟩
  unfold evaluateTreeBody seqs
  run_vcg [hcoreF]
  all_goals
    simp_all [NodeBodyContext, NodeBodyResult, EvalFields, EvalStorage,
      ScanInstallContext, ScanStaticContext]
  all_goals try exact hsymbolAddr
  all_goals try exact hsymbolRead
  all_goals try exact hkB
  all_goals omega

end Lax842588Proofs.AutomatonRamCorrectness
