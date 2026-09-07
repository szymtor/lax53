import Lax53.AutomatonLinearTime
import Lax53Proofs.AutomatonRamArenaEvaluatorCorrectness

/-!
Intrinsic size and cost bounds used to transfer the structural-arena IMP+
execution to the public word-RAM theorem.
-/

namespace Lax53Proofs.AutomatonRamArenaBounds

set_option maxRecDepth 5000
set_option maxHeartbeats 3000000

open Lax13Proofs.Imp
open Lax13Proofs.Compile
open Lax13Proofs.Transfer
open Lax53.ValueTranslations
open Lax53.RankedTree
open Lax53.StructuralRepresentations
open Lax53.TreeModelCheckingEncoding
open Lax53.AutomatonLinearTime
open Lax53Proofs.AutomatonTableEncoding
open Lax53Proofs.AutomatonRamArenaCorrectness
open Lax53Proofs.AutomatonRamCorrectness
open Lax53Proofs.AutomatonRamArenaTreeInvariant
open Lax53Proofs.AutomatonRamArenaTreeLoop
open Lax53Proofs.AutomatonRamArenaReadTree
open Lax53Proofs.AutomatonRamArenaPrepare
open Lax53Proofs.AutomatonRamBackend
open Lax53Proofs.AutomatonRamArenaEvaluatorCorrectness
open Lax58.StructuralPresentation
open Lax58.StructuralPresentation.Presentation
open Lax58.StructuralCombinators

/-- Exact constructor-node count of the automatically derived automaton
presentation. -/
private theorem derivedNat_size (n : Nat) :
    (derivedPresentation : Presentation Nat).structuralSize n = 1 := by
  simpa [derivedPresentation] using sizeLaws.{0, 0}.nat n

private theorem derivedNatList_size (xs : List Nat) :
    (derivedPresentation : Presentation (List Nat)).structuralSize xs =
      1 + 2 * xs.length := by
  rw [show (derivedPresentation : Presentation (List Nat)) =
      list (derivedPresentation : Presentation Nat) by rfl]
  rw [sizeLaws.{0, 0}.list]
  change 1 + xs.length + (xs.map fun _ => 1).sum =
    1 + 2 * xs.length
  simp
  ring

private theorem derivedTransition_size (transition : TransitionCode) :
    (derivedPresentation : Presentation TransitionCode).structuralSize
        transition = 5 + 2 * transition.2.2.length := by
  rw [show (derivedPresentation : Presentation TransitionCode) =
      prod (derivedPresentation : Presentation Nat)
        (prod (derivedPresentation : Presentation Nat)
          (derivedPresentation : Presentation (List Nat))) by rfl]
  rw [sizeLaws.{0, 0}.prod, sizeLaws.{0, 0}.prod,
    derivedNat_size, derivedNat_size,
    derivedNatList_size]
  ring

private theorem derivedTransitionList_size (transitions : List TransitionCode) :
    (derivedPresentation : Presentation (List TransitionCode)).structuralSize
        transitions =
      1 + 6 * transitions.length +
        2 * (transitions.map fun transition => transition.2.2.length).sum := by
  rw [show (derivedPresentation : Presentation (List TransitionCode)) =
      list (derivedPresentation : Presentation TransitionCode) by rfl]
  rw [sizeLaws.{0, 0}.list]
  induction transitions with
  | nil => simp
  | cons transition transitions ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [derivedTransition_size]
      omega

private theorem derivedAutomatonBody_size (body : AutomatonCode) :
    (derivedPresentation : Presentation AutomatonCode).structuralSize body =
      5 + 6 * body.2.1.length +
        2 * (body.2.1.map fun transition => transition.2.2.length).sum +
        2 * body.2.2.length := by
  rw [show (derivedPresentation : Presentation AutomatonCode) =
      prod (derivedPresentation : Presentation Nat)
        (prod (derivedPresentation : Presentation (List TransitionCode))
          (derivedPresentation : Presentation (List Nat))) by rfl]
  rw [sizeLaws.{0, 0}.prod, sizeLaws.{0, 0}.prod, derivedNat_size,
    derivedTransitionList_size, derivedNatList_size]
  ring

theorem automatonSize_eq (M : EncodedAutomaton) :
    automatonSize M =
      7 + 2 * M.1.length + 6 * M.2.2.1.length +
        2 * (M.2.2.1.map fun transition => transition.2.2.length).sum +
        2 * M.2.2.2.length := by
  rw [automatonSize, automatonPresentation]
  rw [show (derivedPresentation : Presentation EncodedAutomaton) =
      prod (derivedPresentation : Presentation RankedAlphabetCode)
        (derivedPresentation : Presentation AutomatonCode) by rfl]
  rw [sizeLaws.{0, 0}.prod, derivedNatList_size,
    derivedAutomatonBody_size]
  ring

private theorem fields_nodes (fields : List Raw) :
    (Raw.fields fields).nodes =
      1 + fields.length + (fields.map Raw.nodes).sum := by
  induction fields with
  | nil => simp [Raw.fields, Raw.nodes]
  | cons field fields ih =>
      simp [Raw.fields, Raw.nodes, ih]
      omega

theorem inputStructuralSize_eq (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    inputStructuralSize M t =
      automatonSize M + (treeStructure M.1 t).nodes + 5 := by
  simp [inputStructuralSize, automatonTreeRaw, Raw.constructor, Raw.nodes,
    fields_nodes, automatonSize, Presentation.structuralSize]
  omega

theorem treeSize_le_treeStructure_nodes (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    treeSize t ≤ (treeStructure alphabet t).nodes := by
  induction t with
  | node symbol children ih =>
      have hsum :
          (List.ofFn fun i => treeSize (children i)).sum ≤
            (List.ofFn fun i => (treeStructure alphabet (children i)).nodes).sum := by
        rw [List.ofFn_eq_map, List.ofFn_eq_map]
        apply List.sum_le_sum
        intro i _
        exact ih i
      calc
        treeSize (.node symbol children) =
            1 + (List.ofFn fun i => treeSize (children i)).sum := rfl
        _ ≤ 1 +
            (List.ofFn fun i => (treeStructure alphabet (children i)).nodes).sum :=
          Nat.add_le_add_left hsum 1
        _ ≤ (treeStructure alphabet (.node symbol children)).nodes := by
          simp [treeStructure, Raw.constructor, Raw.nodes, fields_nodes,
            Function.comp_def]
          omega

theorem treeStructure_nodes_add_one (alphabet : RankedAlphabetCode)
    (t : Tree alphabet.toRankedAlphabet) :
    (treeStructure alphabet t).nodes + 1 = 6 * treeSize t := by
  induction t with
  | node symbol children ih =>
      have hfunctions :
          (fun i => (treeStructure alphabet (children i)).nodes + 1) =
            (fun i => 6 * treeSize (children i)) := by
        funext i
        exact ih i
      have hsums := congrArg List.sum (congrArg List.ofFn hfunctions)
      simp only [List.ofFn_eq_map] at hsums
      rw [List.sum_map_mul_left] at hsums
      have hsum :
          (List.ofFn fun i => (treeStructure alphabet (children i)).nodes).sum +
              alphabet.toRankedAlphabet.rank symbol =
            6 * (List.ofFn fun i => treeSize (children i)).sum := by
        simpa [List.ofFn_eq_map] using hsums
      have hsymbolRaw :
          ((Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin alphabet.length).toRaw
            symbol).nodes = 1 := rfl
      simp only [List.ofFn_eq_map] at hsum
      simp [treeStructure, treeSize, Raw.constructor, Raw.nodes, fields_nodes,
        Function.comp_def, List.ofFn_eq_map, hsymbolRaw]
      omega

theorem automatonSize_le_inputStructuralSize (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    automatonSize M ≤ inputStructuralSize M t := by
  rw [inputStructuralSize_eq]
  omega

theorem treeSize_le_inputStructuralSize (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    treeSize t ≤ inputStructuralSize M t := by
  rw [inputStructuralSize_eq]
  exact (treeSize_le_treeStructure_nodes M.1 t).trans (by omega)

theorem alphabetLength_le_automatonSize (M : EncodedAutomaton) :
    M.1.length ≤ automatonSize M := by
  rw [automatonSize_eq]
  omega

theorem transitionCount_le_automatonSize (M : EncodedAutomaton) :
    M.2.2.1.length ≤ automatonSize M := by
  rw [automatonSize_eq]
  omega

theorem acceptingCount_le_automatonSize (M : EncodedAutomaton) :
    M.2.2.2.length ≤ automatonSize M := by
  rw [automatonSize_eq]
  omega

theorem transitionChildrenSum_le_automatonSize (M : EncodedAutomaton) :
    (M.2.2.1.map fun transition => transition.2.2.length).sum ≤
      automatonSize M := by
  rw [automatonSize_eq]
  omega

private theorem nat_le_sum_of_mem {value : Nat} {values : List Nat}
    (hvalue : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => simp at hvalue
  | cons head tail ih =>
      simp only [List.mem_cons] at hvalue
      rcases hvalue with rfl | hvalue
      · simp
      · exact (ih hvalue).trans (by simp)

theorem transitionChildrenLength_le_automatonSize (M : EncodedAutomaton)
    {transition : TransitionCode} (htransition : transition ∈ M.2.2.1) :
    transition.2.2.length ≤ automatonSize M := by
  have hmem : transition.2.2.length ∈
      M.2.2.1.map (fun transition => transition.2.2.length) :=
    List.mem_map.mpr ⟨transition, htransition, rfl⟩
  exact (nat_le_sum_of_mem hmem).trans
    (transitionChildrenSum_le_automatonSize M)

theorem maximumRank_le_automatonWorkSize (M : EncodedAutomaton) :
    maximumRank M.1 ≤ automatonWorkSize M := by
  simp [automatonWorkSize]

theorem automatonSize_le_automatonWorkSize (M : EncodedAutomaton) :
    automatonSize M ≤ automatonWorkSize M := by
  simp [automatonWorkSize]

private theorem prod_left_max_le {α β : Type} (A : Presentation α)
    (B : Presentation β) (x : α) (y : β) :
    A.maxNat x ≤ (prod A B).maxNat (x, y) := by
  simp [Presentation.maxNat, prod, Raw.maxNat]

private theorem prod_right_max_le {α β : Type} (A : Presentation α)
    (B : Presentation β) (x : α) (y : β) :
    B.maxNat y ≤ (prod A B).maxNat (x, y) := by
  simp [Presentation.maxNat, prod, Raw.maxNat]

private theorem list_member_max_le {α : Type} (P : Presentation α)
    {x : α} {xs : List α} (hx : x ∈ xs) :
    P.maxNat x ≤ (list P).maxNat xs := by
  induction xs with
  | nil => simp at hx
  | cons head tail ih =>
      simp only [List.mem_cons] at hx
      simp only [Presentation.maxNat, list, listToRaw, Raw.maxNat]
      rcases hx with rfl | hx
      · exact Nat.le_max_left _ _
      · exact (ih hx).trans (Nat.le_max_right _ _)

private theorem automatonRaw_max_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    (automatonPresentation.toRaw M).maxNat ≤ inputPayloadMax M t := by
  simp [inputPayloadMax, automatonTreeRaw, Raw.constructor, Raw.fields,
    Raw.maxNat]

private theorem alphabetRaw_max_le_automatonRaw (M : EncodedAutomaton) :
    ((derivedPresentation : Presentation RankedAlphabetCode).toRaw M.1).maxNat ≤
      (automatonPresentation.toRaw M).maxNat := by
  simpa [automatonPresentation, derivedPresentation] using
    prod_left_max_le
      (derivedPresentation : Presentation RankedAlphabetCode)
      (derivedPresentation : Presentation AutomatonCode) M.1 M.2

private theorem bodyRaw_max_le_automatonRaw (M : EncodedAutomaton) :
    ((derivedPresentation : Presentation AutomatonCode).toRaw M.2).maxNat ≤
      (automatonPresentation.toRaw M).maxNat := by
  simpa [automatonPresentation, derivedPresentation] using
    prod_right_max_le
      (derivedPresentation : Presentation RankedAlphabetCode)
      (derivedPresentation : Presentation AutomatonCode) M.1 M.2

theorem alphabetPayload_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {rank : Nat} (hrank : rank ∈ M.1) :
    rank ≤ inputPayloadMax M t := by
  have hmember := list_member_max_le
    (derivedPresentation : Presentation Nat) hrank
  have hnat :
      (derivedPresentation : Presentation Nat).maxNat rank = rank := by
    rfl
  rw [hnat] at hmember
  exact hmember.trans ((alphabetRaw_max_le_automatonRaw M).trans
    (automatonRaw_max_le_inputPayloadMax M t))

theorem stateCount_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : M.2.1 ≤ inputPayloadMax M t := by
  have hbody :
      (derivedPresentation : Presentation Nat).maxNat M.2.1 ≤
        (derivedPresentation : Presentation AutomatonCode).maxNat M.2 := by
    simpa [derivedPresentation] using
      prod_left_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation
          (List TransitionCode × List Nat)) M.2.1 M.2.2
  change M.2.1 ≤ _ at hbody
  exact hbody.trans ((bodyRaw_max_le_automatonRaw M).trans
    (automatonRaw_max_le_inputPayloadMax M t))

private theorem transitionRaw_max_le_automatonRaw (M : EncodedAutomaton)
    {transition : TransitionCode} (htransition : transition ∈ M.2.2.1) :
    (derivedPresentation : Presentation TransitionCode).maxNat transition ≤
      (automatonPresentation.toRaw M).maxNat := by
  have hlist := list_member_max_le
    (derivedPresentation : Presentation TransitionCode) htransition
  have htail :
      (derivedPresentation : Presentation (List TransitionCode)).maxNat M.2.2.1 ≤
        (derivedPresentation : Presentation
          (List TransitionCode × List Nat)).maxNat M.2.2 := by
    simpa [derivedPresentation] using
      prod_left_max_le
        (derivedPresentation : Presentation (List TransitionCode))
        (derivedPresentation : Presentation (List Nat)) M.2.2.1 M.2.2.2
  have hbody :
      (derivedPresentation : Presentation
        (List TransitionCode × List Nat)).maxNat M.2.2 ≤
        (derivedPresentation : Presentation AutomatonCode).maxNat M.2 := by
    simpa [derivedPresentation] using
      prod_right_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation
          (List TransitionCode × List Nat)) M.2.1 M.2.2
  exact hlist.trans (htail.trans (hbody.trans
    (bodyRaw_max_le_automatonRaw M)))

theorem transitionSymbol_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {transition : TransitionCode}
    (htransition : transition ∈ M.2.2.1) :
    transition.1 ≤ inputPayloadMax M t := by
  have hfield :
      (derivedPresentation : Presentation Nat).maxNat transition.1 ≤
        (derivedPresentation : Presentation TransitionCode).maxNat transition := by
    simpa [derivedPresentation] using
      prod_left_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation (Nat × List Nat))
        transition.1 transition.2
  change transition.1 ≤ _ at hfield
  exact hfield.trans ((transitionRaw_max_le_automatonRaw M htransition).trans
    (automatonRaw_max_le_inputPayloadMax M t))

theorem transitionParent_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {transition : TransitionCode}
    (htransition : transition ∈ M.2.2.1) :
    transition.2.1 ≤ inputPayloadMax M t := by
  have hinner :
      (derivedPresentation : Presentation Nat).maxNat transition.2.1 ≤
        (derivedPresentation : Presentation (Nat × List Nat)).maxNat
          transition.2 := by
    simpa [derivedPresentation] using
      prod_left_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation (List Nat))
        transition.2.1 transition.2.2
  have houter :
      (derivedPresentation : Presentation (Nat × List Nat)).maxNat transition.2 ≤
        (derivedPresentation : Presentation TransitionCode).maxNat transition := by
    simpa [derivedPresentation] using
      prod_right_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation (Nat × List Nat))
        transition.1 transition.2
  change transition.2.1 ≤ _ at hinner
  exact hinner.trans (houter.trans
    ((transitionRaw_max_le_automatonRaw M htransition).trans
      (automatonRaw_max_le_inputPayloadMax M t)))

theorem transitionChild_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {transition : TransitionCode}
    (htransition : transition ∈ M.2.2.1) {child : Nat}
    (hchild : child ∈ transition.2.2) :
    child ≤ inputPayloadMax M t := by
  have hmember := list_member_max_le
    (derivedPresentation : Presentation Nat) hchild
  change child ≤
    (derivedPresentation : Presentation (List Nat)).maxNat transition.2.2 at hmember
  have hinner :
      (derivedPresentation : Presentation (List Nat)).maxNat transition.2.2 ≤
        (derivedPresentation : Presentation (Nat × List Nat)).maxNat
          transition.2 := by
    simpa [derivedPresentation] using
      prod_right_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation (List Nat))
        transition.2.1 transition.2.2
  have houter :
      (derivedPresentation : Presentation (Nat × List Nat)).maxNat transition.2 ≤
        (derivedPresentation : Presentation TransitionCode).maxNat transition := by
    simpa [derivedPresentation] using
      prod_right_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation (Nat × List Nat))
        transition.1 transition.2
  exact hmember.trans (hinner.trans (houter.trans
    ((transitionRaw_max_le_automatonRaw M htransition).trans
      (automatonRaw_max_le_inputPayloadMax M t))))

theorem acceptingState_le_inputPayloadMax (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {state : Nat}
    (hstate : state ∈ M.2.2.2) : state ≤ inputPayloadMax M t := by
  have hmember := list_member_max_le
    (derivedPresentation : Presentation Nat) hstate
  change state ≤
    (derivedPresentation : Presentation (List Nat)).maxNat M.2.2.2 at hmember
  have htail :
      (derivedPresentation : Presentation (List Nat)).maxNat M.2.2.2 ≤
        (derivedPresentation : Presentation
          (List TransitionCode × List Nat)).maxNat M.2.2 := by
    simpa [derivedPresentation] using
      prod_right_max_le
        (derivedPresentation : Presentation (List TransitionCode))
        (derivedPresentation : Presentation (List Nat)) M.2.2.1 M.2.2.2
  have hbody :
      (derivedPresentation : Presentation
        (List TransitionCode × List Nat)).maxNat M.2.2 ≤
        (derivedPresentation : Presentation AutomatonCode).maxNat M.2 := by
    simpa [derivedPresentation] using
      prod_right_max_le
        (derivedPresentation : Presentation Nat)
        (derivedPresentation : Presentation
          (List TransitionCode × List Nat)) M.2.1 M.2.2
  exact hmember.trans (htail.trans (hbody.trans
    ((bodyRaw_max_le_automatonRaw M).trans
      (automatonRaw_max_le_inputPayloadMax M t))))

theorem encodeTransitionFixed_value_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {transition : TransitionCode}
    (htransition : transition ∈ M.2.2.1) {value : Nat}
    (hvalue : value ∈ encodeTransitionFixed (maximumRank M.1) transition) :
    value ≤ max (automatonWorkSize M) (inputPayloadMax M t) := by
  simp only [encodeTransitionFixed, List.mem_cons, List.mem_map] at hvalue
  rcases hvalue with rfl | rfl | rfl | ⟨index, _, rfl⟩
  · exact (transitionSymbol_le_inputPayloadMax M t htransition).trans
      (Nat.le_max_right _ _)
  · exact (transitionParent_le_inputPayloadMax M t htransition).trans
      (Nat.le_max_right _ _)
  · exact (transitionChildrenLength_le_automatonSize M htransition).trans
      ((automatonSize_le_automatonWorkSize M).trans (Nat.le_max_left _ _))
  · by_cases hindex : index < transition.2.2.length
    · rw [List.getD_eq_getElem _ _ hindex]
      exact (transitionChild_le_inputPayloadMax M t htransition
        (List.getElem_mem hindex)).trans (Nat.le_max_right _ _)
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hindex)]
      exact Nat.zero_le _

theorem encodeAutomaton_value_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) {value : Nat}
    (hvalue : value ∈ encodeAutomaton M) :
    value ≤ max (automatonWorkSize M) (inputPayloadMax M t) := by
  rw [encodeAutomaton_eq] at hvalue
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvalue
  rcases hvalue with hbeforeAccepting | haccepting
  · rcases hbeforeAccepting with hbeforeCount | hacceptingCount
    · rcases hbeforeCount with hheader | htransition
      · rcases hheader with halphabet | hmetadata
        · rcases halphabet with halphabetLength | hrank
          · subst value
            exact (alphabetLength_le_automatonSize M).trans
              ((automatonSize_le_automatonWorkSize M).trans
                (Nat.le_max_left _ _))
          · exact (alphabetPayload_le_inputPayloadMax M t hrank).trans
              (Nat.le_max_right _ _)
        · rcases hmetadata with hstateCount | htransitionCount | hmaximumRank
          · subst value
            exact (stateCount_le_inputPayloadMax M t).trans
              (Nat.le_max_right _ _)
          · subst value
            exact (transitionCount_le_automatonSize M).trans
              ((automatonSize_le_automatonWorkSize M).trans
                (Nat.le_max_left _ _))
          · subst value
            exact (maximumRank_le_automatonWorkSize M).trans
              (Nat.le_max_left _ _)
      · rw [List.mem_flatMap] at htransition
        obtain ⟨transition, htransition, hrow⟩ := htransition
        exact encodeTransitionFixed_value_le M t htransition hrow
    · subst value
      exact (acceptingCount_le_automatonSize M).trans
        ((automatonSize_le_automatonWorkSize M).trans (Nat.le_max_left _ _))
  · exact (acceptingState_le_inputPayloadMax M t haccepting).trans
      (Nat.le_max_right _ _)

theorem encodeAutomaton_length_le (M : EncodedAutomaton) :
    (encodeAutomaton M).length ≤ 10 * (automatonWorkSize M + 1) ^ 2 := by
  rw [encodeAutomaton_length]
  have hA := (alphabetLength_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hT := (transitionCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hF := (acceptingCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hR := maximumRank_le_automatonWorkSize M
  nlinarith [sq_nonneg (automatonWorkSize M : Int)]

theorem evaluatorWorkspace_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    treeSize t * M.2.2.1.length ≤
      (automatonWorkSize M + 1) ^ 2 *
        (inputStructuralSize M t + inputPayloadMax M t + 1) := by
  have hn := treeSize_le_inputStructuralSize M t
  have hT := (transitionCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hs : 1 ≤ automatonWorkSize M + 1 := by omega
  have hr : inputStructuralSize M t ≤
      inputStructuralSize M t + inputPayloadMax M t + 1 := by omega
  nlinarith [Nat.mul_le_mul hn hT,
    Nat.mul_le_mul (Nat.mul_le_mul hs hs) hr]

theorem evaluatorIndexWork_le (M : EncodedAutomaton) :
    M.1.length + 4 +
        M.2.2.1.length * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) ≤
        20 * (automatonWorkSize M + 1) ^ 2 := by
  have hA := (alphabetLength_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hT := (transitionCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hR := maximumRank_le_automatonWorkSize M
  nlinarith [sq_nonneg (automatonWorkSize M : Int)]

theorem inputStructuralSize_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    inputStructuralSize M t ≤
      12 * (automatonWorkSize M + 1) * (treeSize t + 1) := by
  rw [inputStructuralSize_eq]
  have htree := treeStructure_nodes_add_one M.1 t
  have hautomaton := automatonSize_le_automatonWorkSize M
  have htreePositive := Lax53Proofs.AutomatonRamCorrectness.treeSize_pos M.1 t
  nlinarith [Nat.zero_le (automatonWorkSize M * treeSize t)]

/-- One transition can be decoded within a linear budget in the intrinsic
automaton workload. -/
theorem transitionBodyCost_le (M : EncodedAutomaton)
    {transition : TransitionCode} (htransition : transition ∈ M.2.2.1) :
    transitionBodyCost (maximumRank M.1) transition ≤
      1000 * (automatonWorkSize M + 1) := by
  have hchildren := (transitionChildrenLength_le_automatonSize M htransition).trans
    (automatonSize_le_automatonWorkSize M)
  have hR := maximumRank_le_automatonWorkSize M
  simp [transitionBodyCost, processTransitionChildrenCost,
    transitionChildLoopCost, transitionPaddingLoopCost,
    Cond.size, Expr.size]
  omega

/-- The complete charged structural frontend is quadratic in automaton
workload and linear in tree size. -/
theorem prepareCost_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    prepareCost M t (1000 * (automatonWorkSize M + 1)) ≤
      10000 * (automatonWorkSize M + 1) ^ 2 * (treeSize t + 1) := by
  have hN := inputStructuralSize_le M t
  have hA := (alphabetLength_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hT := (transitionCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hF := (acceptingCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hn := Lax53Proofs.AutomatonRamCorrectness.treeSize_pos M.1 t
  have hmemory :
      (Lax58.WordArena.encodeRaw (automatonTreeRaw M t)).memoryWords =
        3 * inputStructuralSize M t := by
    simpa [inputStructuralSize] using
      Lax58Proofs.WordArena.encodeRaw_memoryWords_proof
        (automatonTreeRaw M t)
  rw [prepareCost]
  simp only [hmemory]
  simp [alphabetLoopCost, readTransitionsCost, transitionLoopCost,
    readAcceptingCost, acceptingLoopCost, readTreeCost,
    treeTraversalLoopCost, transitionCondition, acceptingCondition,
    AutomatonRamArenaProgram.alphabetCondition,
    treeLoopCondition, Cond.size, Expr.size]
  nlinarith [sq_nonneg (automatonWorkSize M : Int),
    Nat.zero_le (automatonWorkSize M * treeSize t)]

/-- Cost of the already verified automaton backend in the same public
workload measure. -/
theorem automatonBackendCost_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    automatonBackendCost M t ≤
      1000 * (automatonWorkSize M + 1) ^ 2 * (treeSize t + 1) := by
  have hT := (transitionCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hF := (acceptingCount_le_automatonSize M).trans
    (automatonSize_le_automatonWorkSize M)
  have hrank := rankSum_encodeTree_add_one M.1 t
  have hn := Lax53Proofs.AutomatonRamCorrectness.treeSize_pos M.1 t
  let s := automatonWorkSize M
  let n := treeSize t
  let T := M.2.2.1.length
  let F := M.2.2.2.length
  have hmeasure : n + rankSum M.1 (encodeTree M.1 t) ≤ 2 * n := by
    dsimp [n]
    omega
  have hsq : (T + 1) ^ 2 ≤ (s + 1) ^ 2 :=
    Nat.pow_le_pow_left (by simpa [s, T] using hT) 2
  have hnode : 300 * (T + 1) ^ 2 *
      (n + rankSum M.1 (encodeTree M.1 t)) ≤
        600 * (s + 1) ^ 2 * n := by
    have hcoef := Nat.mul_le_mul_left 300 hsq
    have hmul := Nat.mul_le_mul hcoef hmeasure
    nlinarith
  have hFT : F * T ≤ s * s := by
    exact Nat.mul_le_mul (by simpa [F, s] using hF)
      (by simpa [T, s] using hT)
  have hrest : (39 * F + 34) * T + 51 ≤
      100 * (s + 1) ^ 2 * (n + 1) := by
    dsimp [s, n, T, F] at hFT ⊢
    nlinarith [sq_nonneg (automatonWorkSize M : Int)]
  unfold automatonBackendCost nodeCoefficient
  dsimp [s, n, T, F] at hnode hrest
  nlinarith

theorem arenaEvaluatorImpCost_le (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    arenaEvaluatorImpCost M t (1000 * (automatonWorkSize M + 1)) ≤
      12000 * (automatonWorkSize M + 1) ^ 2 * (treeSize t + 1) := by
  unfold arenaEvaluatorImpCost
  have hprepare := prepareCost_le M t
  have hbackend := automatonBackendCost_le M t
  nlinarith

/-- Value bound used at the IMP+-to-RAM simulation boundary. It is a fixed
fraction of the public word-resource bound. -/
def evaluatorValueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) : Nat :=
  uniformWordBound 1000 M t

private theorem resourceBase_bounds (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    let base := (automatonWorkSize M + 1) ^ 2 *
      (inputStructuralSize M t + inputPayloadMax M t + 1)
    automatonWorkSize M + 1 ≤ base ∧
      inputStructuralSize M t + 1 ≤ base ∧
      inputPayloadMax M t + 1 ≤ base ∧ 0 < base := by
  intro base
  let s := automatonWorkSize M
  let N := inputStructuralSize M t
  let m := inputPayloadMax M t
  have hsone : 1 ≤ s + 1 := by omega
  have hsq : 1 ≤ (s + 1) ^ 2 := by
    have := Nat.mul_le_mul hsone hsone
    simpa [pow_two] using this
  have hsquare : s + 1 ≤ (s + 1) ^ 2 := by
    have := Nat.mul_le_mul_left (s + 1) hsone
    simpa [pow_two] using this
  have hfactor : 1 ≤ N + m + 1 := by omega
  have hNfactor : N + 1 ≤ N + m + 1 := by omega
  have hmFactor : m + 1 ≤ N + m + 1 := by omega
  have hsBase := Nat.mul_le_mul hsquare hfactor
  have hNBase := Nat.mul_le_mul hsq hNfactor
  have hmBase := Nat.mul_le_mul hsq hmFactor
  have hpositive : 0 < (s + 1) ^ 2 * (N + m + 1) :=
    Nat.mul_pos (by omega) (by omega)
  dsimp [base, s, N, m] at hsBase hNBase hmBase hpositive ⊢
  exact ⟨by simpa using hsBase, by simpa using hNBase,
    by simpa using hmBase, hpositive⟩

theorem valueBound_basic (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    4 < evaluatorValueBound M t ∧
      automatonWorkSize M < evaluatorValueBound M t ∧
      inputStructuralSize M t < evaluatorValueBound M t ∧
      inputPayloadMax M t < evaluatorValueBound M t := by
  let base := (automatonWorkSize M + 1) ^ 2 *
    (inputStructuralSize M t + inputPayloadMax M t + 1)
  have hbase := resourceBase_bounds M t
  dsimp only at hbase
  have hpositive : 0 < base := by simpa [base] using hbase.2.2.2
  have hbaseBound : base < evaluatorValueBound M t := by
    simp [evaluatorValueBound, uniformWordBound, base]
  refine ⟨?_, (by omega), (by omega), (by omega)⟩
  rw [evaluatorValueBound, uniformWordBound, Nat.mul_assoc]
  change 4 < 1000 * base
  omega

theorem arenaMemory_lt_valueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    (Lax58.WordArena.encodeRaw (automatonTreeRaw M t)).memoryWords <
      evaluatorValueBound M t := by
  rw [show
    (Lax58.WordArena.encodeRaw (automatonTreeRaw M t)).memoryWords =
      3 * inputStructuralSize M t by
    simpa [inputStructuralSize] using
      Lax58Proofs.WordArena.encodeRaw_memoryWords_proof
        (automatonTreeRaw M t)]
  let base := (automatonWorkSize M + 1) ^ 2 *
    (inputStructuralSize M t + inputPayloadMax M t + 1)
  have hbase := resourceBase_bounds M t
  dsimp only at hbase
  have hN : inputStructuralSize M t + 1 ≤ base := by
    simpa [base] using hbase.2.1
  rw [evaluatorValueBound, uniformWordBound, Nat.mul_assoc]
  change 3 * inputStructuralSize M t < 1000 * base
  omega

theorem arenaInput_values_lt_valueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    ∀ value ∈ automatonInput M t, value < evaluatorValueBound M t := by
  have hbasic := valueBound_basic M t
  apply Lax58Proofs.WordArena.encodeRaw_toInput_lt
    (automatonTreeRaw M t) (evaluatorValueBound M t)
  · simpa [inputPayloadMax] using hbasic.2.2.2
  · have hmemory := Nat.le_of_lt (arenaMemory_lt_valueBound M t)
    rw [Lax58Proofs.WordArena.encodeRaw_memoryWords_proof] at hmemory
    simpa [inputStructuralSize] using hmemory

theorem encodeAutomaton_length_lt_valueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    (encodeAutomaton M).length < evaluatorValueBound M t := by
  have hlength := encodeAutomaton_length_le M
  let base := (automatonWorkSize M + 1) ^ 2 *
    (inputStructuralSize M t + inputPayloadMax M t + 1)
  have hfactor : 1 ≤
      inputStructuralSize M t + inputPayloadMax M t + 1 := by omega
  have hsquare : (automatonWorkSize M + 1) ^ 2 ≤ base := by
    dsimp [base]
    simpa using Nat.mul_le_mul_left ((automatonWorkSize M + 1) ^ 2) hfactor
  have hpositive : 0 < base := by
    simpa [base] using (resourceBase_bounds M t).2.2.2
  rw [evaluatorValueBound, uniformWordBound, Nat.mul_assoc]
  change (encodeAutomaton M).length < 1000 * base
  omega

theorem encodeAutomaton_values_lt_valueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    ∀ value ∈ encodeAutomaton M, value < evaluatorValueBound M t := by
  intro value hvalue
  have hle := encodeAutomaton_value_le M t hvalue
  have hbasic := valueBound_basic M t
  exact hle.trans_lt (max_lt hbasic.2.1 hbasic.2.2.2)

theorem evaluatorWorkspace_lt_valueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    treeSize t * M.2.2.1.length < evaluatorValueBound M t := by
  have hworkspace := evaluatorWorkspace_le M t
  have hpositive : 0 < (automatonWorkSize M + 1) ^ 2 *
      (inputStructuralSize M t + inputPayloadMax M t + 1) :=
    (resourceBase_bounds M t).2.2.2
  rw [evaluatorValueBound, uniformWordBound, Nat.mul_assoc]
  change treeSize t * M.2.2.1.length <
    1000 * ((automatonWorkSize M + 1) ^ 2 *
      (inputStructuralSize M t + inputPayloadMax M t + 1))
  nlinarith

theorem evaluatorIndexWork_lt_valueBound (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) :
    M.1.length + 4 +
        M.2.2.1.length * (maximumRank M.1 + 3) +
      (maximumRank M.1 + 3) < evaluatorValueBound M t := by
  have hwork := evaluatorIndexWork_le M
  have hfactor : 1 ≤
      inputStructuralSize M t + inputPayloadMax M t + 1 := by omega
  have hscaled := Nat.mul_le_mul_left (20 * (automatonWorkSize M + 1) ^ 2)
    hfactor
  have hpositive : 0 < (automatonWorkSize M + 1) ^ 2 *
      (inputStructuralSize M t + inputPayloadMax M t + 1) :=
    (resourceBase_bounds M t).2.2.2
  rw [evaluatorValueBound, uniformWordBound, Nat.mul_assoc]
  change M.1.length + 4 +
      M.2.2.1.length * (maximumRank M.1 + 3) +
        (maximumRank M.1 + 3) <
    1000 * ((automatonWorkSize M + 1) ^ 2 *
      (inputStructuralSize M t + inputPayloadMax M t + 1))
  nlinarith

theorem arenaLayout_fitsWords (M : EncodedAutomaton)
    (t : Tree M.1.toRankedAlphabet) (w : Nat)
    (hword : uniformWordBound 1000000 M t ≤ 2 ^ w) :
    Lax53Proofs.AutomatonRamArenaProgram.layout.FitsWords
      (evaluatorValueBound M t) w := by
  apply fitsWords_of_max_le (by exact (valueBound_basic M t).1.trans' (by omega))
  apply le_trans (b := uniformWordBound 1000000 M t)
  · apply max_le
    · simp [evaluatorValueBound, uniformWordBound]
    · simp [Layout.span, Lax53Proofs.AutomatonRamArenaProgram.layout,
        Lax53Proofs.AutomatonRamProgram.layout, evaluatorValueBound,
        uniformWordBound]
      have hpositive : 0 < (automatonWorkSize M + 1) ^ 2 *
          (inputStructuralSize M t + inputPayloadMax M t + 1) :=
        (resourceBase_bounds M t).2.2.2
      nlinarith
  · exact hword

end Lax53Proofs.AutomatonRamArenaBounds
