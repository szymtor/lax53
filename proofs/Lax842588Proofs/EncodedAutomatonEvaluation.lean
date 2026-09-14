import Lax842588.TreeModelCheckingEncoding

namespace Lax842588Proofs.EncodedAutomatonEvaluation

open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588.ValueTranslations

/-- The child-state list selected by a transition agrees with the lists of
states already computed for the ordered children. -/
def ChildrenAgree (childStates : CodeString) (reachable : List CodeString) : Bool :=
  childStates.length == reachable.length &&
    (childStates.zip reachable).all fun qr => qr.2.contains qr.1

/-- Sparse bottom-up evaluation of an encoded automaton. The result lists the
states to which the automaton can run on the supplied tree. -/
def reachable (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    Tree alphabet.toRankedAlphabet → CodeString
  | .node a children =>
      let childReachable := List.ofFn fun i => reachable alphabet M (children i)
      M.2.1.filterMap fun tr =>
        if tr.1 = a.val && tr.2.1 < M.1 &&
            ChildrenAgree tr.2.2 childReachable then
          some tr.2.1
        else none

theorem mem_reachable_lt (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) {q : Nat}
    (hq : q ∈ reachable alphabet M t) : q < M.1 := by
  cases t with
  | node a children =>
      simp only [reachable, List.mem_filterMap] at hq
      obtain ⟨tr, _, htr⟩ := hq
      split at htr
      · rename_i hvalid
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
        have heq : tr.2.1 = q := by simpa only [Option.some.injEq] using htr
        omega
      · simp at htr

theorem childrenAgree_iff {k : Nat} (childStates : List Nat)
    (reachable : Fin k → CodeString) (hlen : childStates.length = k) :
    ChildrenAgree childStates (List.ofFn reachable) = true ↔
      ∀ i : Fin k, childStates.get ⟨i.val, by omega⟩ ∈ reachable i := by
  simp only [ChildrenAgree, Bool.and_eq_true, beq_iff_eq, List.length_ofFn,
    List.all_eq_true]
  constructor
  · rintro ⟨_, h⟩ i
    let j : Fin childStates.length := ⟨i.val, by omega⟩
    have hm : (childStates.get j, reachable i) =
        (childStates.zip (List.ofFn reachable)).get ⟨i.val, by
          simp [List.length_zip, hlen]⟩ := by
      simp [j]
    let zi : Fin (childStates.zip (List.ofFn reachable)).length := ⟨i.val, by
      simp [List.length_zip, hlen]⟩
    have hz := h ((childStates.zip (List.ofFn reachable)).get zi)
      (List.get_mem _ zi)
    rw [← hm] at hz
    exact List.contains_iff_mem.mp hz
  · intro h
    refine ⟨hlen, ?_⟩
    intro qr hqr
    obtain ⟨i, rfl⟩ := List.get_of_mem hqr
    have hik : i.val < k := by
      have := i.isLt
      simp [List.length_zip, hlen] at this
      exact this
    let j : Fin k := ⟨i.val, hik⟩
    rw [List.get_eq_getElem, List.getElem_zip]
    simp only [List.getElem_ofFn]
    exact List.contains_iff_mem.mpr (by simpa [j] using h j)

theorem mem_reachable_iff_runsTo (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) (q : Fin M.1) :
    q.val ∈ reachable alphabet M t ↔ (M.toAutomaton alphabet).RunsTo t q := by
  induction t generalizing q with
  | node a children ih =>
      simp only [reachable, List.mem_filterMap]
      constructor
      · rintro ⟨tr, htrmem, htr⟩
        split at htr
        · rename_i hvalid
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hvalid
          rcases hvalid with ⟨⟨hsymbol, hparentBound⟩, hagree⟩
          have hparent : tr.2.1 = q.val := by simpa only [Option.some.injEq] using htr
          have hlen : tr.2.2.length = alphabet.toRankedAlphabet.rank a := by
            have hh := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hagree).1
            simpa using hh
          let childStates : Fin (alphabet.toRankedAlphabet.rank a) → Fin M.1 := fun i =>
            ⟨tr.2.2.get ⟨i.val, by omega⟩,
              mem_reachable_lt alphabet M (children i) <|
                (childrenAgree_iff tr.2.2
                  (fun i => reachable alphabet M (children i)) hlen).mp hagree i⟩
          refine ⟨childStates, ?_, ?_⟩
          · simp only [AutomatonCode.toAutomaton]
            apply List.any_eq_true.mpr
            refine ⟨tr, htrmem, ?_⟩
            simp only [decide_eq_true_eq]
            refine ⟨hsymbol, hparent, ?_⟩
            apply List.ext_get
            · simp [hlen]
            · intro n h₁ h₂
              simp [childStates]
          · intro i
            apply (ih i (childStates i)).mp
            exact (childrenAgree_iff tr.2.2
              (fun i => reachable alphabet M (children i)) hlen).mp hagree i
        · simp at htr
      · rintro ⟨childStates, htransition, hruns⟩
        simp only [AutomatonCode.toAutomaton] at htransition
        obtain ⟨tr, htrmem, hmatch⟩ := List.any_eq_true.mp htransition
        simp only [decide_eq_true_eq] at hmatch
        rcases hmatch with ⟨hsymbol, hparent, hchildren⟩
        refine ⟨tr, htrmem, ?_⟩
        have hsymbolB : decide (tr.1 = a.val) = true := decide_eq_true hsymbol
        have hparentB : decide (tr.2.1 < M.1) = true := decide_eq_true (hparent ▸ q.isLt)
        have hlen : tr.2.2.length = alphabet.toRankedAlphabet.rank a := by simp [hchildren]
        have hagree : ChildrenAgree tr.2.2
            (List.ofFn fun i => reachable alphabet M (children i)) = true := by
          apply (childrenAgree_iff tr.2.2
            (fun i => reachable alphabet M (children i)) hlen).mpr
          intro i
          have hlist : tr.2.2.get ⟨i.val, by omega⟩ = (childStates i).val := by
            have heq := congrArg (fun xs : List Nat => xs[i.val]?) hchildren
            have hi : i.val < tr.2.2.length := by omega
            change tr.2.2[i.val]? = _ at heq
            simp only [List.getElem?_eq_getElem hi, List.getElem?_ofFn] at heq
            simpa using heq
          rw [hlist]
          exact (ih i (childStates i)).mpr (hruns i)
        simp only [hsymbolB, hparentB, hagree, Bool.true_and, ite_true]
        exact congrArg some hparent

/-- The sparse evaluator decides acceptance. -/
def accepts (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) : Bool :=
  (reachable alphabet M t).any fun q => M.2.2.contains q

theorem accepts_eq_true_iff (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    accepts alphabet M t = true ↔ (M.toAutomaton alphabet).Accepts t := by
  rw [accepts, List.any_eq_true]
  constructor
  · rintro ⟨q, hqreach, hqaccept⟩
    let state : Fin M.1 := ⟨q, mem_reachable_lt alphabet M t hqreach⟩
    exact ⟨state, by simpa [AutomatonCode.toAutomaton] using hqaccept,
      (mem_reachable_iff_runsTo alphabet M t state).mp hqreach⟩
  · rintro ⟨q, hqaccept, hqrun⟩
    exact ⟨q.val, (mem_reachable_iff_runsTo alphabet M t q).mpr hqrun,
      by simpa [AutomatonCode.toAutomaton] using hqaccept⟩

end Lax842588Proofs.EncodedAutomatonEvaluation
