import Lax842588Proofs.ArenaSemantics
import Lax842588Proofs.AutomatonRamArenaProgram
import Lax842588Proofs.AutomatonRamCorrectness

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

set_option maxHeartbeats 3000000
open Classical

open Lax865980Proofs.Imp
open Lax865980Proofs.Reasoning
open Lax842588Proofs.ArrayInput
open Lax842588.RankedTree
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.ArenaSemantics
open Lax842588Proofs.AutomatonRamArenaProgram
open Lax842588Proofs.AutomatonRamCorrectness
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

def ArenaLoaded (I : WordImage) (sigma : Env) : Prop :=
  sigma.arrs "Arena" = arenaWords I ∧
    sigma.vars "root" = I.root ∧
    sigma.vars "arenaLen" = I.memoryWords ∧ sigma.inp = []

theorem readArena_spec (B : Nat) (raw : Raw)
    (hmemB : (encodeRaw raw).memoryWords < B)
    (hvaluesB : ∀ v ∈ (encodeRaw raw).toInput, v < B) :
    Spec B
      (fun sigma => (sigma.arrs "Arena").length =
          (encodeRaw raw).memoryWords ∧
        sigma.inp = (encodeRaw raw).toInput)
      readArena
      (fun _ sigma' => ArenaLoaded (encodeRaw raw) sigma')
      (12 * (encodeRaw raw).memoryWords + 20) := by
  let I := encodeRaw raw
  have hrootLast : I.root + 3 = I.memoryWords := by
    exact Lax560851Proofs.WordArena.encodeRaw_root_last raw
  have hmemoryB : I.memoryWords < B := by
    simpa [I] using hmemB
  have hrootB : I.root < B := by omega
  have harenaValues : ∀ v ∈ arenaWords I, v < B := by
    intro v hv
    apply hvaluesB v
    simpa [I, WordImage.toInput, arenaWords] using
      (List.mem_cons_of_mem I.root hv)
  have hread := (Lax842588Proofs.ArrayInput.readArr_spec B
    "Arena" "arenaRead" "arenaLen" "arenaValue"
    (arenaWords I) [] (by decide) (by decide) (by decide)
    (by simpa [arenaWords, WordImage.memoryWords] using hmemoryB)
    harenaValues).frame
  have hcore : Spec B
      (fun sigma => (sigma.arrs "Arena").length =
          (encodeRaw raw).memoryWords ∧
        sigma.inp = (encodeRaw raw).toInput)
      readArena
      (fun _ sigma' => ArenaLoaded (encodeRaw raw) sigma')
      (1 + (1 + ((.add (.var "root") (.lit 3) : Expr).size +
        (12 * (arenaWords I).length + 6 + 1)))) := by
    unfold readArena AutomatonRamProgram.seqs
    run_vcg [hread]
    all_goals simp_all [I, ArenaLoaded, WordImage.toInput, arenaWords,
      WordImage.memoryWords]
  exact hcore.mono (by
    simp [Expr.size, I, arenaWords, WordImage.memoryWords]
    omega)

structure InstancePointers (I : WordImage) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) where
  fields : Nat
  automaton : Nat
  treeTail : Nat
  tree : Nat
  alphabet : Nat
  body : Nat
  rootValid : I.ValidAddress I.root
  fieldsValid : I.ValidAddress fields
  automatonValid : I.ValidAddress automaton
  treeTailValid : I.ValidAddress treeTail
  fieldsWord : (arenaWords I).getD (I.root + 2) 0 = fields
  automatonWord : (arenaWords I).getD (fields + 1) 0 = automaton
  treeTailWord : (arenaWords I).getD (fields + 2) 0 = treeTail
  treeWord : (arenaWords I).getD (treeTail + 1) 0 = tree
  alphabetWord : (arenaWords I).getD (automaton + 1) 0 = alphabet
  bodyWord : (arenaWords I).getD (automaton + 2) 0 = body
  automatonRep : I.Represents automaton
    (Lax842588.StructuralRepresentations.automatonPresentation.toRaw M)
  alphabetRep : I.Represents alphabet
    ((derivedPresentation : Presentation RankedAlphabetCode).toRaw M.1)
  bodyRep : I.Represents body
    ((derivedPresentation : Presentation AutomatonCode).toRaw M.2)
  treeRep : I.Represents tree (treeStructure M.1 t)

theorem instancePointers (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    Nonempty (InstancePointers (encodeRaw (automatonTreeRaw M t)) M t) := by
  let I := encodeRaw (automatonTreeRaw M t)
  have hroot : I.Represents I.root (automatonTreeRaw M t) := by
    exact Lax560851.WordArena.encodeRaw_represents _
  change I.Represents I.root
    (Raw.constructor "automatonAcceptance"
      [Lax842588.StructuralRepresentations.automatonPresentation.toRaw M,
        treeStructure M.1 t]) at hroot
  obtain ⟨nameAddress, fieldsAddress, hrootTag, hnameWord, hfieldsWord,
      hnameRep, hfieldsRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.pair_words hroot
  obtain ⟨automatonAddress, treeTailAddress, hfieldsTag, hautomatonWord,
      htreeTailWord, hautomatonRep, htreeTailRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.fields_cons hfieldsRep
  obtain ⟨treeAddress, nilAddress, htailTag, htreeWord, hnilWord,
      htreeRep, hnilRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.fields_cons htreeTailRep
  obtain ⟨alphabetAddress, bodyAddress, hautomatonTag, halphabetWord,
      hbodyWord, halphabetRep, hbodyRep⟩ :=
    Lax842588Proofs.ArenaSemantics.Represents.prod_fields hautomatonRep
  exact ⟨{
    fields := fieldsAddress
    automaton := automatonAddress
    treeTail := treeTailAddress
    tree := treeAddress
    alphabet := alphabetAddress
    body := bodyAddress
    rootValid := Lax842588Proofs.ArenaSemantics.Represents.valid hroot
    fieldsValid := Lax842588Proofs.ArenaSemantics.Represents.valid hfieldsRep
    automatonValid := Lax842588Proofs.ArenaSemantics.Represents.valid hautomatonRep
    treeTailValid := Lax842588Proofs.ArenaSemantics.Represents.valid htreeTailRep
    fieldsWord := hfieldsWord
    automatonWord := hautomatonWord
    treeTailWord := htreeTailWord
    treeWord := htreeWord
    alphabetWord := halphabetWord
    bodyWord := hbodyWord
    automatonRep := hautomatonRep
    alphabetRep := halphabetRep
    bodyRep := hbodyRep
    treeRep := htreeRep
  }⟩

def InstanceOpened (I : WordImage) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    ∃ p : InstancePointers I M t,
      sigma.vars "instanceFields" = p.fields ∧
      sigma.vars "automatonRoot" = p.automaton ∧
      sigma.vars "treeFieldTail" = p.treeTail ∧
      sigma.vars "treeRoot" = p.tree ∧
      sigma.vars "alphabetCursor" = p.alphabet ∧
      sigma.vars "bodyRoot" = p.body

def InstanceOpenedAt (I : WordImage) {M : EncodedAutomaton}
    {t : Tree M.1.toRankedAlphabet} (p : InstancePointers I M t)
    (sigma : Env) : Prop :=
  ArenaLoaded I sigma ∧
    sigma.vars "instanceFields" = p.fields ∧
    sigma.vars "automatonRoot" = p.automaton ∧
    sigma.vars "treeFieldTail" = p.treeTail ∧
    sigma.vars "treeRoot" = p.tree ∧
    sigma.vars "alphabetCursor" = p.alphabet ∧
    sigma.vars "bodyRoot" = p.body

theorem openInstanceAt_spec (B : Nat) (I : WordImage)
    {M : EncodedAutomaton} {t : Tree M.1.toRankedAlphabet}
    (p : InstancePointers I M t)
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
  have hautomatonLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length p.automatonValid
  have htreeTailLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length p.treeTailValid
  have htreeLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid p.treeRep)
  have halphabetLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid p.alphabetRep)
  have hbodyLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length
      (Lax842588Proofs.ArenaSemantics.Represents.valid p.bodyRep)
  have hfieldsGet : (arenaWords I)[I.root + 2] = p.fields := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem hrootLen]
    exact p.fieldsWord
  have hautomatonGet : (arenaWords I)[p.fields + 1] = p.automaton := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact p.automatonWord
  have htreeTailGet : (arenaWords I)[p.fields + 2] = p.treeTail := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem hfieldsLen]
    exact p.treeTailWord
  have htreeGet : (arenaWords I)[p.treeTail + 1] = p.tree := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact p.treeWord
  have halphabetGet : (arenaWords I)[p.automaton + 1] = p.alphabet := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
    exact p.alphabetWord
  have hbodyGet : (arenaWords I)[p.automaton + 2] = p.body := by
    rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem hautomatonLen]
    exact p.bodyWord
  have hfieldsGetD : ((arenaWords I)[I.root + 2]?).getD 0 = p.fields := by
    simpa [List.getD_eq_getElem?_getD] using p.fieldsWord
  have hautomatonGetD : ((arenaWords I)[p.fields + 1]?).getD 0 = p.automaton := by
    simpa [List.getD_eq_getElem?_getD] using p.automatonWord
  have htreeTailGetD : ((arenaWords I)[p.fields + 2]?).getD 0 = p.treeTail := by
    simpa [List.getD_eq_getElem?_getD] using p.treeTailWord
  have htreeGetD : ((arenaWords I)[p.treeTail + 1]?).getD 0 = p.tree := by
    simpa [List.getD_eq_getElem?_getD] using p.treeWord
  have halphabetGetD : ((arenaWords I)[p.automaton + 1]?).getD 0 = p.alphabet := by
    simpa [List.getD_eq_getElem?_getD] using p.alphabetWord
  have hbodyGetD : ((arenaWords I)[p.automaton + 2]?).getD 0 = p.body := by
    simpa [List.getD_eq_getElem?_getD] using p.bodyWord
  have htreeGetDB : ((arenaWords I)[p.treeTail + 1]?).getD 0 < B := by
    rw [htreeGetD]
    omega
  have halphabetGetDB : ((arenaWords I)[p.automaton + 1]?).getD 0 < B := by
    rw [halphabetGetD]
    omega
  have hbodyGetDB : ((arenaWords I)[p.automaton + 2]?).getD 0 < B := by
    rw [hbodyGetD]
    omega
  have harenaLengthEq : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  unfold openInstance AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [InstanceOpenedAt, ArenaLoaded]
  all_goals omega

theorem openInstance_spec (B : Nat) (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet)
    (h0 : 0 < B)
    (hmemB : (encodeRaw (automatonTreeRaw M t)).memoryWords < B)
    (hvaluesB : ∀ v ∈ arenaWords (encodeRaw (automatonTreeRaw M t)), v < B) :
    Spec B (ArenaLoaded (encodeRaw (automatonTreeRaw M t))) openInstance
      (fun _ sigma' =>
        InstanceOpened (encodeRaw (automatonTreeRaw M t)) M t sigma') 40 := by
  let I := encodeRaw (automatonTreeRaw M t)
  obtain ⟨p⟩ := instancePointers M t
  have h := openInstanceAt_spec B I p h0 (by simpa [I] using hmemB)
    (by simpa [I] using hvaluesB)
  apply h.post
  intro _ sigma' _ hopened
  exact ⟨hopened.1, p, hopened.2⟩

end Lax842588Proofs.AutomatonRamArenaCorrectness
