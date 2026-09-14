import Lax842588Proofs.AutomatonRamArenaRead
import Lax842588Proofs.MSORamArenaProgram
import Lax842588.MSOLinearTime

/-!
Semantic pointer certificate and charged opener for the distinguished
`(alphabet, intrinsic sentence, tree)` arena.
-/

namespace Lax842588Proofs.MSORamArenaRead

set_option maxHeartbeats 3000000
open Classical

open FirstOrder
open FirstOrder.Language
open Lax146103.MSOSyntax
open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588.MSOLinearTime
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax842588Proofs.AutomatonRamCorrectness
open Lax842588Proofs.MSORamArenaProgram
open Lax560851.StructuralPresentation
open Lax560851.StructuralPresentation.Presentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- Addresses selected by the three-field constructor spine. Each address is
certified against the exact mathematical value it denotes. -/
structure InstancePointers (I : WordImage) (alphabet : RankedAlphabetCode)
    (phi : Lax146103.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) where
  fields : Nat
  formulaTail : Nat
  treeTail : Nat
  alphabetAddress : Nat
  formulaAddress : Nat
  treeAddress : Nat
  rootValid : I.ValidAddress I.root
  fieldsValid : I.ValidAddress fields
  formulaTailValid : I.ValidAddress formulaTail
  treeTailValid : I.ValidAddress treeTail
  fieldsWord : (arenaWords I).getD (I.root + 2) 0 = fields
  alphabetWord : (arenaWords I).getD (fields + 1) 0 = alphabetAddress
  formulaTailWord : (arenaWords I).getD (fields + 2) 0 = formulaTail
  formulaWord : (arenaWords I).getD (formulaTail + 1) 0 = formulaAddress
  treeTailWord : (arenaWords I).getD (formulaTail + 2) 0 = treeTail
  treeWord : (arenaWords I).getD (treeTail + 1) 0 = treeAddress
  alphabetRep : I.Represents alphabetAddress
    ((derivedPresentation : Presentation RankedAlphabetCode).toRaw alphabet)
  formulaRep : I.Represents formulaAddress (formulaStructure alphabet phi)
  treeRep : I.Represents treeAddress (treeStructure alphabet t)

theorem instancePointers (alphabet : RankedAlphabetCode)
    (phi : Lax146103.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    Nonempty (InstancePointers (encodeRaw (msoTreeRaw alphabet phi t))
      alphabet phi t) := by
  let I := encodeRaw (msoTreeRaw alphabet phi t)
  have hroot : I.Represents I.root (msoTreeRaw alphabet phi t) :=
    Lax560851Proofs.WordArena.encodeRaw_represents_proof _
  change I.Represents I.root
    (Raw.constructor "msoModelChecking"
      [(derivedPresentation : Presentation RankedAlphabetCode).toRaw alphabet,
        formulaStructure alphabet phi, treeStructure alphabet t]) at hroot
  obtain ⟨_, fieldsAddress, _, _, hfieldsWord, _, hfieldsRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.pair_words hroot
  obtain ⟨alphabetAddress, formulaTailAddress, _, halphabetWord,
      hformulaTailWord, halphabetRep, hformulaTailRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  obtain ⟨formulaAddress, treeTailAddress, _, hformulaWord, htreeTailWord,
      hformulaRep, htreeTailRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.fields_cons hformulaTailRep
  obtain ⟨treeAddress, _, _, htreeWord, _, htreeRep, _⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.fields_cons htreeTailRep
  exact ⟨{
    fields := fieldsAddress
    formulaTail := formulaTailAddress
    treeTail := treeTailAddress
    alphabetAddress := alphabetAddress
    formulaAddress := formulaAddress
    treeAddress := treeAddress
    rootValid := Lax842588Proofs.ArenaSemantics.Represents.valid hroot
    fieldsValid := Lax842588Proofs.ArenaSemantics.Represents.valid hfieldsRep
    formulaTailValid :=
      Lax842588Proofs.ArenaSemantics.Represents.valid hformulaTailRep
    treeTailValid := Lax842588Proofs.ArenaSemantics.Represents.valid htreeTailRep
    fieldsWord := hfieldsWord
    alphabetWord := halphabetWord
    formulaTailWord := hformulaTailWord
    formulaWord := hformulaWord
    treeTailWord := htreeTailWord
    treeWord := htreeWord
    alphabetRep := halphabetRep
    formulaRep := hformulaRep
    treeRep := htreeRep
  }⟩

def InstanceOpenedAt (I : WordImage) {alphabet : RankedAlphabetCode}
    {phi : Lax146103.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet)}
    {t : Tree alphabet.toRankedAlphabet}
    (p : InstancePointers I alphabet phi t) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "instanceFields" = p.fields ∧
    sigma.vars "alphabetCursor" = p.alphabetAddress ∧
    sigma.vars "formulaFieldTail" = p.formulaTail ∧
    sigma.vars "formulaRoot" = p.formulaAddress ∧
    sigma.vars "treeFieldTail" = p.treeTail ∧
    sigma.vars "treeRoot" = p.treeAddress

theorem openInstanceAt_spec (B : Nat) (I : WordImage)
    {alphabet : RankedAlphabetCode}
    {phi : Lax146103.MSOSyntax.Sentence
      (treeSignature alphabet.toRankedAlphabet)}
    {t : Tree alphabet.toRankedAlphabet}
    (p : InstancePointers I alphabet phi t)
    (h0 : 0 < B) (hmemB : I.memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords I, v < B) :
    Spec B (ArenaLoaded I) openInstance
      (fun _ sigma' => InstanceOpenedAt I p sigma') 40 := by
  have hgetB (i : Nat) : (arenaWords I).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hvaluesB
  have hgetOptB (i : Nat) : ((arenaWords I)[i]?).getD 0 < B := by
    simpa [List.getD_eq_getElem?_getD] using hgetB i
  have harenaLen : (arenaWords I).length < B := by
    simpa [arenaWords, WordImage.memoryWords] using hmemB
  have hrootLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length p.rootValid
  have hfieldsLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length p.fieldsValid
  have hformulaTailLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      p.formulaTailValid
  have htreeTailLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length p.treeTailValid
  have halphabetB : p.alphabetAddress < B := by
    have hvalid := Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid p.alphabetRep)
    omega
  have hformulaB : p.formulaAddress < B := by
    have hvalid := Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid p.formulaRep)
    omega
  have htreeB : p.treeAddress < B := by
    have hvalid := Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid p.treeRep)
    omega
  have hfieldsGetD : ((arenaWords I)[I.root + 2]?).getD 0 = p.fields := by
    simpa [List.getD_eq_getElem?_getD] using p.fieldsWord
  have halphabetGetD :
      ((arenaWords I)[p.fields + 1]?).getD 0 = p.alphabetAddress := by
    simpa [List.getD_eq_getElem?_getD] using p.alphabetWord
  have hformulaTailGetD :
      ((arenaWords I)[p.fields + 2]?).getD 0 = p.formulaTail := by
    simpa [List.getD_eq_getElem?_getD] using p.formulaTailWord
  have hformulaGetD :
      ((arenaWords I)[p.formulaTail + 1]?).getD 0 = p.formulaAddress := by
    simpa [List.getD_eq_getElem?_getD] using p.formulaWord
  have htreeTailGetD :
      ((arenaWords I)[p.formulaTail + 2]?).getD 0 = p.treeTail := by
    simpa [List.getD_eq_getElem?_getD] using p.treeTailWord
  have htreeGetD :
      ((arenaWords I)[p.treeTail + 1]?).getD 0 = p.treeAddress := by
    simpa [List.getD_eq_getElem?_getD] using p.treeWord
  unfold openInstance Lax842588Proofs.AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [InstanceOpenedAt, ArenaLoaded]
  all_goals omega

end Lax842588Proofs.MSORamArenaRead
