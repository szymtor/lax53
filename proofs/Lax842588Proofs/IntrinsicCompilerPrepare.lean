import Lax842588Proofs.IntrinsicCompilerFromArena
import Lax842588Proofs.FormulaArenaTraversalRead

/-!
The public certified-input frontend establishes the measured compiler's
working-array precondition. Reading the arena, opening its three fields,
decoding the alphabet, and traversing the intrinsic sentence are all charged.
-/

namespace Lax842588Proofs.IntrinsicCompilerPrepare

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations Lax842588.MSOLinearTime
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.FormulaArenaTraversalInit
open Lax842588Proofs.FormulaArenaTraversalInvariant Lax842588Proofs.FormulaArenaTraversalRead
open Lax560851.WordArena

def formulaArrays : List String :=
  ["FormulaOrder", "FormulaFOOrder", "FormulaSOOrder", "FormulaRootStack",
    "FormulaFOStack", "FormulaSOStack", "FormulaPhaseStack"]

def Capacity (B count : Nat) (σ : Env) : Prop :=
  ∀ a ∈ formulaArrays, count ≤ (σ.arrs a).length ∧ (σ.arrs a).length < B

def Initial (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) (σ : Env) : Prop :=
  (σ.arrs "Arena").length = (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords ∧
    alphabet.length + 4 ≤ (σ.arrs "P").length ∧ (σ.arrs "P").length < B ∧
    Capacity B (postorder alphabet φ).length σ ∧
    σ.inp = Lax842588.MSOLinearTime.modelCheckingInput alphabet φ t

def program : Com :=
  .seq AutomatonRamArenaProgram.readArena
    (.seq MSORamArenaProgram.openInstance
      (.seq AutomatonRamArenaProgram.readAlphabet MSORamArenaProgram.readFormula))

def timeBound (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : Nat :=
  (12 * (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords + 20) + 40 +
    (alphabetLoopCost alphabet + 50) + formulaReadCost alphabet φ

theorem program_spec (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet)
    (p : MSORamArenaRead.InstancePointers (encodeRaw (msoTreeRaw alphabet φ t)) alphabet φ t)
    (h4 : 4 < B) (hmem : (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords < B)
    (hvalues : ∀ value ∈ arenaWords (encodeRaw (msoTreeRaw alphabet φ t)), value < B)
    (htags : FormulaTagBounds B) (halphabet : alphabet.length < B)
    (hwidth : Lax842588.TreeModelCheckingEncoding.maximumRank alphabet + 3 < B)
    (hsteps : traversalSteps alphabet φ < B)
    (hscopes : ∀ o ∈ postorder alphabet φ, o.fo < B ∧ o.so < B ∧
      2 ^ o.fo < B ∧ 2 ^ o.so < B ∧
      MarkedAlphabetEncoding.symbolCount alphabet o.fo o.so < B) :
    Spec B (Initial B alphabet φ t) program
      (fun _ σ => IntrinsicCompilerFromArena.Ready B (encodeRaw (msoTreeRaw alphabet φ t))
        alphabet (postorder alphabet φ) σ ∧
        ArenaLoaded (encodeRaw (msoTreeRaw alphabet φ t)) σ ∧
        σ.vars "treeRoot" = p.treeAddress) (timeBound alphabet φ t) := by
  let I := encodeRaw (msoTreeRaw alphabet φ t)
  have h0 : 0 < B := by omega
  have hrootB : I.root < B := by
    have hr := Lax560851Proofs.WordArena.encodeRaw_root_last (msoTreeRaw alphabet φ t)
    dsimp [I]
    omega
  have hinputB : ∀ value ∈ I.toInput, value < B := by
    intro value hv
    simp only [WordImage.toInput, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hrootB
    · exact hvalues value (by simpa [I, arenaWords] using hv)
  intro σ hσ
  obtain ⟨hArena, hPspace, hPB, hcapacity, hinput⟩ := hσ
  obtain ⟨σ1, hread, hloaded⟩ := readArena_spec B (msoTreeRaw alphabet φ t) hmem hinputB
    σ ⟨hArena, by simpa [Lax842588.MSOLinearTime.modelCheckingInput] using hinput⟩
  obtain ⟨σ2, hopen, hopened⟩ := MSORamArenaRead.openInstanceAt_spec B I p h0 hmem hvalues σ1 hloaded
  have hP2 : (σ2.arrs "P").length = (σ.arrs "P").length :=
    Lax842588Proofs.Run.arrayLength_eq (hread.seq hopen) "P"
  obtain ⟨hloaded2, _, hcursor, _, hformulaRoot, _, htreeRoot⟩ := hopened
  have hαready : AlphabetReady B I alphabet σ2 :=
    ⟨hloaded2, by omega, by omega, p.alphabetAddress, hcursor, p.alphabetRep⟩
  obtain ⟨σ3, hα, hαread, _⟩ := readAlphabet_spec B I alphabet h4 hmem hvalues hwidth σ2 hαready
  have hprefixRun := hread.seq (hopen.seq hα)
  have hcapacity3 : Capacity B (postorder alphabet φ).length σ3 := by
    intro a ha
    simpa [Lax842588Proofs.Run.arrayLength_eq hprefixRun a] using hcapacity a ha
  have hroot3 : σ3.vars "formulaRoot" = p.formulaAddress :=
    (hα.frame_var "formulaRoot" (by decide)).trans hformulaRoot
  have hr := hcapacity3 "FormulaRootStack" (by simp [formulaArrays])
  have hf := hcapacity3 "FormulaFOStack" (by simp [formulaArrays])
  have hs := hcapacity3 "FormulaSOStack" (by simp [formulaArrays])
  have hp := hcapacity3 "FormulaPhaseStack" (by simp [formulaArrays])
  have ho := hcapacity3 "FormulaOrder" (by simp [formulaArrays])
  have hfo := hcapacity3 "FormulaFOOrder" (by simp [formulaArrays])
  have hso := hcapacity3 "FormulaSOOrder" (by simp [formulaArrays])
  have hpositive := List.length_pos_of_ne_nil (postorder_ne_nil alphabet φ)
  have htarget := postorder_length_le_traversalSteps alphabet φ
  have hφready : FormulaReadReady B I alphabet φ p.formulaAddress σ3 :=
    ⟨⟨hαread.1, hroot3, p.formulaRep, by omega, by omega, by omega, by omega,
        hr.2, hf.2, hs.2, hp.2⟩,
      ho.1, hfo.1, hso.1, hr.1, hf.1, hs.1, hp.1, ho.2, hfo.2, hso.2, by omega, hsteps,
      fun o ho => ⟨(hscopes o ho).1, (hscopes o ho).2.1⟩⟩
  obtain ⟨σ4, hφ, hcomplete⟩ := readFormula_spec B I alphabet φ p.formulaAddress
    (by omega) hmem hvalues htags σ3 hφready
  obtain ⟨⟨produced, frames, hstate⟩, hcount, _, _, horder⟩ := hcomplete
  have hA4 : σ4.vars "A" = alphabet.length :=
    (hφ.frame_var "A" (by decide)).trans hαread.2.2.2.1
  have hcontext : IntrinsicFormulaInput.Context B I alphabet (postorder alphabet φ) σ4 := by
    apply IntrinsicFormulaInput.context_of_order B I alphabet _ σ4 hstate.arenaLoaded horder
      _ hA4 halphabet hscopes
    intro a ha
    simp at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨hstate.rootOrderCapacity, hstate.rootOrderLengthB⟩
    · exact ⟨hstate.foOrderCapacity, hstate.foOrderLengthB⟩
    · exact ⟨hstate.soOrderCapacity, hstate.soOrderLengthB⟩
  have hprefix : CompilerArrayPacking.Prefix "P" (alphabet.length :: alphabet) σ4 := by
    have hh := IntrinsicAlphabetInput.prefix_of_alphabetRead B I alphabet σ3 hαread
    simpa [CompilerArrayPacking.Prefix, hφ.frame_arr "P" (by decide)] using hh
  have htree4 : σ4.vars "treeRoot" = p.treeAddress := by
    rw [hφ.frame_var "treeRoot" (by decide), hα.frame_var "treeRoot" (by decide)]
    exact htreeRoot
  exact ⟨σ4, (hread.seq (hopen.seq (hα.seq hφ))).mono (by unfold timeBound; omega),
    ⟨hcontext, hcount, hprefix, hA4⟩, hstate.arenaLoaded, htree4⟩

end Lax842588Proofs.IntrinsicCompilerPrepare
