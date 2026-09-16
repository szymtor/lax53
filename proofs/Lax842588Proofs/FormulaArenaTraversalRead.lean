import Lax842588Proofs.FormulaArenaTraversalLoop

/-!
Composition of the charged formula-stack initializer with the complete
intrinsic-sentence traversal.
-/

namespace Lax842588Proofs.FormulaArenaTraversalRead

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open Lax146103.MSOSyntax
open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.FormulaArenaTraversalOrder
open Lax842588Proofs.FormulaArenaTraversalInit
open Lax842588Proofs.FormulaArenaTraversalInvariant
open Lax842588Proofs.FormulaArenaTraversalLoop
open Lax842588Proofs.MSORamArenaProgram
open Lax560851.WordArena

def FormulaReadReady (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (formulaRoot : Nat) (sigma : Env) : Prop :=
  FormulaTraversalReady B I alphabet phi formulaRoot sigma ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaOrder").length ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaFOOrder").length ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaSOOrder").length ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaRootStack").length ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaFOStack").length ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaSOStack").length ∧
    (postorder alphabet phi).length ≤
      (sigma.arrs "FormulaPhaseStack").length ∧
    (sigma.arrs "FormulaOrder").length < B ∧
    (sigma.arrs "FormulaFOOrder").length < B ∧
    (sigma.arrs "FormulaSOOrder").length < B ∧
    (postorder alphabet phi).length < B ∧
    traversalSteps alphabet phi < B ∧
    FormulaScopesFit B alphabet (postorder alphabet phi)

def FormulaReadComplete (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (sigma : Env) : Prop :=
  FormulaLoopInv B I alphabet phi sigma ∧
    sigma.vars "formulaCount" = (postorder alphabet phi).length ∧
    sigma.vars "formulaSteps" = traversalSteps alphabet phi ∧
    sigma.vars "formulaDepth" = 0 ∧
    FormulaOrderRep I alphabet (postorder alphabet phi)
      (sigma.arrs "FormulaOrder") (sigma.arrs "FormulaFOOrder")
      (sigma.arrs "FormulaSOOrder")

def formulaReadCost (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet)) : Nat :=
  50 + formulaTraversalLoopCost alphabet phi

theorem readFormula_spec (B : Nat) (I : WordImage)
    (alphabet : RankedAlphabetCode)
    (phi : Sentence (treeSignature alphabet.toRankedAlphabet))
    (formulaRoot : Nat)
    (h2 : 2 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ value ∈ arenaWords I, value < B)
    (htags : FormulaTagBounds B) :
    Spec B (FormulaReadReady B I alphabet phi formulaRoot) readFormula
      (fun _ sigma' => FormulaReadComplete B I alphabet phi sigma')
      (formulaReadCost alphabet phi) := by
  intro sigma hready
  rcases hready with ⟨hinitReady, hrootOrderCapacity,
    hfoOrderCapacity, hsoOrderCapacity, hrootStackCapacity,
    hfoStackCapacity, hsoStackCapacity, hphaseStackCapacity,
    hrootOrderLengthB, hfoOrderLengthB, hsoOrderLengthB,
    htargetB, hstepsB, hscopes⟩
  have hinit :=
    (initializeFormulaTraversal_spec B I alphabet phi formulaRoot
      (by omega) hmemB).frame
  obtain ⟨sigma1, hrun1,
      ⟨hinitialized, hvars1, harrs1, hinp1, hout1⟩⟩ :=
    hinit.run hinitReady
  have hrootStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun1 "FormulaRootStack"
  have hfoStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun1 "FormulaFOStack"
  have hsoStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun1 "FormulaSOStack"
  have hphaseStackLength :=
    Lax842588Proofs.Run.arrayLength_eq hrun1 "FormulaPhaseStack"
  have hloopState : FormulaLoopState B I alphabet phi []
      [initialFrame alphabet phi] sigma1 :=
    initialized_loopState B I alphabet phi sigma1 hinitialized htargetB
      hstepsB
      (by simpa [harrs1 "FormulaOrder" (by decide)] using hrootOrderCapacity)
      (by simpa [harrs1 "FormulaFOOrder" (by decide)] using hfoOrderCapacity)
      (by simpa [harrs1 "FormulaSOOrder" (by decide)] using hsoOrderCapacity)
      (by simpa [hrootStackLength] using hrootStackCapacity)
      (by simpa [hfoStackLength] using hfoStackCapacity)
      (by simpa [hsoStackLength] using hsoStackCapacity)
      (by simpa [hphaseStackLength] using hphaseStackCapacity)
      (by simpa [harrs1 "FormulaOrder" (by decide)] using hrootOrderLengthB)
      (by simpa [harrs1 "FormulaFOOrder" (by decide)] using hfoOrderLengthB)
      (by simpa [harrs1 "FormulaSOOrder" (by decide)] using hsoOrderLengthB)
      hscopes
  have hloop := (formulaTraversalLoop_completed_spec B I alphabet phi h2
    hmemB hvaluesB htags).frame
  obtain ⟨sigma2, hrun2,
      ⟨hcomplete, hvars2, harrs2, hinp2, hout2⟩⟩ :=
    hloop.run ⟨[], [initialFrame alphabet phi], hloopState⟩
  have hrun : Run B readFormula sigma sigma2 (formulaReadCost alphabet phi) := by
    unfold readFormula formulaReadCost
    exact hrun1.seq hrun2
  exact ⟨sigma2, hrun, hcomplete⟩

end Lax842588Proofs.FormulaArenaTraversalRead
