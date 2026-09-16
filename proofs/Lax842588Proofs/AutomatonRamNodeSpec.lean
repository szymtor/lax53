import Lax842588Proofs.AutomatonRamNode

namespace Lax842588Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamProgram
open Lax842588Proofs.AutomatonTableEncoding
open Lax842588Proofs.EncodedAutomatonWordEvaluation

def nodeOutput (M : EncodedAutomaton) (stack : List CodeString)
    (symbol : Nat) : CodeString :=
  let k := M.1.getD symbol 0
  parentStates M.2 symbol (childRows stack.reverse stack.length k)

def nodeStates (M : EncodedAutomaton) (states : List Nat)
    (stack : List CodeString) (symbol : Nat) : List Nat :=
  let k := M.1.getD symbol 0
  writePrefix states ((stack.length - k) * M.2.2.1.length)
    (nodeOutput M stack symbol) (nodeOutput M stack symbol).length

def nodeLengths (M : EncodedAutomaton) (lengths : List Nat)
    (stack : List CodeString) (symbol : Nat) : List Nat :=
  let k := M.1.getD symbol 0
  lengths.set (stack.length - k) (nodeOutput M stack symbol).length

def ScanInstallContext (M : EncodedAutomaton) (states lengths : List Nat)
    (stack : List CodeString) (symbol : Nat) (sigma : Env) : Prop :=
  ScanStaticContext M states lengths stack.length (M.1.getD symbol 0) symbol sigma ∧
    RowsRep states lengths M.2.2.1.length stack.reverse

def ScanInstallResult (M : EncodedAutomaton) (states lengths : List Nat)
    (stack : List CodeString) (symbol : Nat) (sigma : Env) : Prop :=
  sigma.arrs "S" = nodeStates M states stack symbol ∧
    sigma.arrs "L" = nodeLengths M lengths stack symbol ∧
    (sigma.arrs "O").length = M.2.2.1.length ∧
    sigma.vars "depth" = (pushSymbol M.1 M.2 stack symbol).length ∧
    RowsRep (sigma.arrs "S") (sigma.arrs "L") M.2.2.1.length
      (pushSymbol M.1 M.2 stack symbol).reverse

theorem scanInstall_spec (B : Nat) (M : EncodedAutomaton)
    (states lengths : List Nat) (stack : List CodeString) (symbol : Nat)
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
    (hrep : RowsRep states lengths M.2.2.1.length stack.reverse) :
    Spec B (ScanInstallContext M states lengths stack symbol)
      (.seq scanTransitions installParent)
      (fun _ sigma' => ScanInstallResult M states lengths stack symbol sigma')
      (nodeCoreCost M (M.1.getD symbol 0)) := by
  let k := M.1.getD symbol 0
  let children := childRows stack.reverse stack.length k
  let output := parentStates M.2 symbol children
  let newStates := writePrefix states ((stack.length - k) * M.2.2.1.length)
    output output.length
  let newLengths := lengths.set (stack.length - k) output.length
  have hkR : k ≤ maximumRank M.1 :=
    maximumRank_ge M.1 symbol hsymbolIndex
  have hkB : k < B := by
    have h := getD_lt_of_mem_bound (i := symbol + 1) h0 hparameterB
    rw [encodeAutomaton_rank M symbol hsymbolIndex] at h
    simpa [k] using h
  have hdepthB : stack.length < B := lt_trans hstackRoom hlengthsLenB
  have hdepthRows : stack.length ≤ lengths.length := by
    simpa using hrep.1
  have hlenLe : ∀ row < stack.length,
      lengths.getD row 0 ≤ M.2.2.1.length := by
    intro row hrow
    exact rowsRep_row_length_le hrep (by simpa using hrow)
  have hspan : ∀ j < k, (stack.length - k + j) * M.2.2.1.length +
      lengths.getD (stack.length - k + j) 0 ≤ states.length := by
    intro j hj
    have hrow : stack.length - k + j < stack.reverse.length := by simp; omega
    have hlen := rowsRep_row_length_le hrep hrow
    calc
      (stack.length - k + j) * M.2.2.1.length +
          lengths.getD (stack.length - k + j) 0 ≤
          (stack.length - k + j) * M.2.2.1.length + M.2.2.1.length :=
        Nat.add_le_add_left hlen _
      _ = (stack.length - k + j + 1) * M.2.2.1.length := by ring
      _ ≤ lengths.length * M.2.2.1.length :=
        Nat.mul_le_mul_right _ (by simp at hrow; omega)
      _ = states.length := hcapacity.symm
  have haddr : ∀ j < k, (stack.length - k + j) * M.2.2.1.length +
      lengths.getD (stack.length - k + j) 0 < B := by
    intro j hj
    exact lt_of_le_of_lt (hspan j hj) hstatesLenB
  have hscan : Spec B (ScanInstallContext M states lengths stack symbol)
      scanTransitions
      (fun _ sigma' => ScanInv M states lengths stack.length k symbol sigma' ∧
        sigma'.vars "tr" = M.2.2.1.length)
      (transitionScanCost M k) := by
    have hscan0 := scanTransitions_spec B M states lengths stack.length k symbol h0 h1
      hparameterB hstatesB hlengthsB hparameterLenB hstatesLenB hlengthsLenB
      hkR hsafe hdepthRows hwidthB hdepthB hkB hsymbolB hQB hTB hlenLe hspan
      haddr hworkB
    exact hscan0.pre (fun _ h => h.1)
  have hinstall : Spec B
      (fun sigma => ScanInv M states lengths stack.length k symbol sigma ∧
        sigma.vars "tr" = M.2.2.1.length)
      installParent
      (fun _ sigma' => ScanInstallResult M states lengths stack symbol sigma')
      (34 * M.2.2.1.length + 30) := by
    intro sigma hsigma
    rcases hsigma.1 with ⟨hstatic, _, hscratch, hprefix⟩
    rcases hstatic with ⟨hP, hS, hL, hOlen, hrecords, hT, hR, hwidth,
      hQ, hdepth, hk, hsym⟩
    rw [hsigma.2] at hscratch hprefix
    have houtEq := transitionOutputs_eq_parentStates M
      (rows := stack.reverse) (depth := stack.length) (k := k) (symbol := symbol)
      hrep (by simp) hsafe hkR
    change transitionOutputs M states lengths stack.length k symbol M.2.2.1.length =
      output at houtEq
    rw [houtEq] at hscratch hprefix
    have houtputLen : output.length ≤ M.2.2.1.length := by
      exact parentStates_length_le M.2 symbol children
    have houtputLenB : output.length < B := lt_of_le_of_lt houtputLen hTB
    have houtputB : ∀ q ∈ output, q < B := by
      intro q hq
      exact lt_trans (mem_parentStates_lt M.2 symbol q children hq) hQB
    have htarget : stack.length - k < lengths.length := by omega
    have houtputSpan : (stack.length - k) * M.2.2.1.length + output.length ≤
        states.length := by
      calc
        (stack.length - k) * M.2.2.1.length + output.length ≤
            (stack.length - k) * M.2.2.1.length + M.2.2.1.length :=
          Nat.add_le_add_left houtputLen _
        _ = (stack.length - k + 1) * M.2.2.1.length := by ring
        _ ≤ lengths.length * M.2.2.1.length :=
          Nat.mul_le_mul_right _ (by omega)
        _ = states.length := hcapacity.symm
    have hinst0 := installParent_spec B states lengths (sigma.arrs "O") output
      M.2.2.1.length stack.length k h0 h1 houtputB hprefix
      (hOlen.trans_lt hTB) hstatesLenB hlengthsLenB hTB hdepthB hkB hsafe
      htarget houtputLenB houtputSpan
    have hpre : sigma.arrs "S" = states ∧ sigma.arrs "L" = lengths ∧
        sigma.arrs "O" = sigma.arrs "O" ∧
        sigma.vars "T" = M.2.2.1.length ∧
        sigma.vars "depth" = stack.length ∧ sigma.vars "k" = k ∧
        sigma.vars "scratchLen" = output.length :=
      ⟨hS, hL, rfl, hT, hdepth, hk, hscratch⟩
    obtain ⟨sigma', hrun, hpost⟩ := hinst0.frame sigma hpre
    rcases hpost with ⟨⟨hS', hL', hdepth'⟩, hvars, harrs, hinp, hout⟩
    refine ⟨sigma', hrun.mono ?_, ?_⟩
    · exact Nat.add_le_add_right (Nat.mul_le_mul_left 34 houtputLen) 30
    · have hnewRep := rowsRep_after_install (k := k) (output := output) hrep
        (by simpa using! hsafe) (by simpa using htarget) houtputLen
        (by simpa using houtputSpan)
      rw [collapseRows_pushSymbol M.1 M.2 stack symbol hsafe] at hnewRep
      have hpushLen : (pushSymbol M.1 M.2 stack symbol).length =
          stack.length - k + 1 := by
        simp [pushSymbol, k]
      refine ⟨?_, ?_, (congrArg List.length (harrs "O" (by decide))).trans hOlen,
        hdepth'.trans hpushLen.symm, ?_⟩
      · simpa [nodeStates, nodeOutput, k, children, output] using hS'
      · simpa [nodeLengths, nodeOutput, k, children, output] using hL'
      · rw [hS', hL']
        simpa [nodeStates, nodeLengths, nodeOutput, k, children, output] using hnewRep
  exact hscan.seq hinstall (fun _ _ _ h => h)
    (fun _ _ _ _ _ h => h)

end Lax842588Proofs.AutomatonRamCorrectness
