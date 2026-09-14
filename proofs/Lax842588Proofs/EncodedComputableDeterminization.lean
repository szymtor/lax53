import Lax842588Proofs.EncodedAutomataComputability
import Lax842588Proofs.FiniteWordStates

namespace Lax842588Proofs.EncodedComputableDeterminization

open Lax842588.ValueTranslations
open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588Proofs.FiniteAutomatonEncoding
open Lax842588Proofs.FiniteWordStates
open Lax842588Proofs.EncodedAutomataOperations
open Lax842588Proofs.EncodedAutomataComputability

/-- Decode a canonical Boolean word state, defaulting to the empty word for
out-of-range state numbers. -/
def subsetBits (n S : Nat) : List Nat := (words 2 n).getD S []

/-- Membership in a subset represented by its canonical Boolean word. -/
def subsetMember (n S q : Nat) : Bool :=
  decide ((subsetBits n S).getD q 0 = 1)

/-- Encode a numeric Boolean predicate on `0, …, n-1` as the index of its
Boolean word in the canonical enumeration. -/
def encodeSubset (n : Nat) (pred : Nat → Bool) : Nat :=
  (words 2 n).idxOf ((List.range n).map fun q => (pred q).toNat)

theorem bits_mem_words (n : Nat) (pred : Nat → Bool) :
    (List.range n).map (fun q => (pred q).toNat) ∈ words 2 n := by
  rw [mem_words_iff]
  constructor
  · simp
  · intro q hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
    cases pred i <;> decide

theorem encodeSubset_lt (n : Nat) (pred : Nat → Bool) :
    encodeSubset n pred < (words 2 n).length := by
  unfold encodeSubset
  exact List.idxOf_lt_length_of_mem (bits_mem_words n pred)

theorem subsetBits_encodeSubset (n : Nat) (pred : Nat → Bool) :
    subsetBits n (encodeSubset n pred) =
      (List.range n).map fun q => (pred q).toNat := by
  unfold subsetBits encodeSubset
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (bits_mem_words n pred))]
  simp only [Option.getD_some]
  exact List.idxOf_get (List.idxOf_lt_length_of_mem (bits_mem_words n pred))

theorem subsetMember_encodeSubset {n q : Nat} (pred : Nat → Bool) (hq : q < n) :
    subsetMember n (encodeSubset n pred) q = pred q := by
  unfold subsetMember
  rw [subsetBits_encodeSubset]
  simp [List.getD_eq_getElem?_getD, hq]

/-- All children selected by a transition belong to their corresponding
represented subsets. -/
def childrenAgree (n : Nat) (childSets qs : List Nat) : Bool :=
  childSets.length == qs.length &&
    (List.range qs.length).all fun i =>
      subsetMember n (childSets.getD i 0) (qs.getD i 0)

/-- Whether `q` belongs to the deterministic successor subset. -/
def nextMember (M : AutomatonCode) (a : Nat) (childSets : List Nat) (q : Nat) : Bool :=
  (words M.1 childSets.length).any fun qs =>
    step M a q qs && childrenAgree M.1 childSets qs

def nextCode (M : AutomatonCode) (a : Nat) (childSets : List Nat) : Nat :=
  encodeSubset M.1 (nextMember M a childSets)

/-- Executable powerset determinization using canonical Boolean words rather
than the library's dependent finite-set encoding. -/
def determinize (alphabet : RankedAlphabetCode) (M : AutomatonCode) : AutomatonCode :=
  FiniteAutomatonEncoding.encode alphabet (words 2 M.1).length
    (fun a S childSets => decide (S = nextCode M a childSets))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)

def subsetFin (n : Nat) (states : Finset (Fin n)) : Fin (words 2 n).length :=
  ⟨encodeSubset n fun q => if h : q < n then decide (⟨q, h⟩ ∈ states) else false,
    encodeSubset_lt n _⟩

@[simp] theorem subsetMember_subsetFin {n : Nat} (states : Finset (Fin n))
    (q : Fin n) : subsetMember n (subsetFin n states).val q.val = decide (q ∈ states) := by
  unfold subsetFin
  rw [subsetMember_encodeSubset _ q.isLt]
  simp [q.isLt]

theorem childrenAgree_subsetFin_iff {n k : Nat}
    (sets : Fin k → Finset (Fin n)) (qs : List Nat)
    (hlen : qs.length = k) (hbound : ∀ q ∈ qs, q < n) :
    childrenAgree n (List.ofFn fun i => (subsetFin n (sets i)).val) qs = true ↔
      ∀ i : Fin k,
        (⟨qs.get ⟨i.val, by omega⟩,
          hbound _ (List.get_mem _ _)⟩ : Fin n) ∈ sets i := by
  unfold childrenAgree
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_ofFn, List.all_eq_true]
  constructor
  · rintro ⟨hlength, hall⟩ i
    have hi : i.val ∈ List.range qs.length := List.mem_range.mpr (by omega)
    have h := hall i.val hi
    have hchild : (List.ofFn fun j => (subsetFin n (sets j)).val).getD i.val 0 =
        (subsetFin n (sets i)).val := by
      simp [List.getD_eq_getElem?_getD, i.isLt]
    have hq : qs.getD i.val 0 = qs.get ⟨i.val, by omega⟩ := by
      simp [List.getD_eq_getElem?_getD, i.isLt, hlen]
    let r : Fin n := ⟨qs.get ⟨i.val, by omega⟩,
      hbound _ (List.get_mem _ _)⟩
    rw [hchild, hq] at h
    change subsetMember n (subsetFin n (sets i)).val r.val = true at h
    rw [subsetMember_subsetFin] at h
    exact of_decide_eq_true h
  · intro h
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    have hiq : i < qs.length := List.mem_range.mp hi
    let j : Fin k := ⟨i, by omega⟩
    have hchild : (List.ofFn fun j => (subsetFin n (sets j)).val).getD i 0 =
        (subsetFin n (sets j)).val := by
      rw [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp [j]
    have hq : qs.getD i 0 = qs.get ⟨i, hiq⟩ := by
      simp [List.getD_eq_getElem?_getD, hiq]
    let r : Fin n := ⟨qs.get ⟨i, hiq⟩,
      hbound _ (List.get_mem _ _)⟩
    rw [hchild, hq]
    change subsetMember n (subsetFin n (sets j)).val r.val = true
    rw [subsetMember_subsetFin]
    exact decide_eq_true (by simpa [j] using h j)

theorem nextMember_subsetFin_iff (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (a : alphabet.toRankedAlphabet.Symbol)
    (sets : Fin (alphabet.toRankedAlphabet.rank a) → Finset (Fin M.1))
    (q : Fin M.1) :
    nextMember M a.val (List.ofFn fun i => (subsetFin M.1 (sets i)).val) q.val = true ↔
      q ∈ Lax842588Proofs.Determinization.step (M.toAutomaton alphabet) a sets := by
  simp only [nextMember, List.any_eq_true,
    Lax842588Proofs.Determinization.mem_step]
  constructor
  · rintro ⟨qs, hqs, htest⟩
    have hword : qs ∈ words M.1 (alphabet.toRankedAlphabet.rank a) := by
      simpa using hqs
    have hlen := (mem_words_iff.mp hword).1
    have hbound := (mem_words_iff.mp hword).2
    rcases Bool.and_eq_true_iff.mp htest with ⟨hstep, hagree⟩
    let childStates : Fin (alphabet.toRankedAlphabet.rank a) → Fin M.1 := fun i =>
      ⟨qs.get ⟨i.val, by omega⟩, hbound _ (List.get_mem _ _)⟩
    refine ⟨childStates, ?_, ?_⟩
    · rw [← step_eq_transition alphabet M a q childStates]
      have heq : List.ofFn (fun i => (childStates i).val) = qs := by
        apply List.ext_get
        · simp [hlen]
        · intro i hi₁ hi₂
          simp [childStates]
      simpa [heq] using hstep
    · exact (childrenAgree_subsetFin_iff sets qs hlen hbound).mp hagree
  · rintro ⟨childStates, hstep, hchildren⟩
    let qs := List.ofFn fun i => (childStates i).val
    have hqs : qs ∈ words M.1 (alphabet.toRankedAlphabet.rank a) :=
      ofFn_mem_words childStates
    refine ⟨qs, by simpa using hqs, Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · rw [step_eq_transition alphabet M a q childStates]
      simpa [qs] using hstep
    · apply (childrenAgree_subsetFin_iff sets qs
        (mem_words_iff.mp hqs).1 (mem_words_iff.mp hqs).2).mpr
      intro i
      simpa [qs] using hchildren i

theorem nextCode_subsetFin (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (a : alphabet.toRankedAlphabet.Symbol)
    (sets : Fin (alphabet.toRankedAlphabet.rank a) → Finset (Fin M.1)) :
    nextCode M a.val (List.ofFn fun i => (subsetFin M.1 (sets i)).val) =
      (subsetFin M.1
        (Lax842588Proofs.Determinization.step (M.toAutomaton alphabet) a sets)).val := by
  unfold nextCode
  change encodeSubset M.1 (fun q =>
      nextMember M a.val (List.ofFn fun i => (subsetFin M.1 (sets i)).val) q) =
    encodeSubset M.1 (fun q => if h : q < M.1 then
      decide ((⟨q, h⟩ : Fin M.1) ∈
        Lax842588Proofs.Determinization.step (M.toAutomaton alphabet) a sets)
      else false)
  unfold encodeSubset
  congr 1
  apply List.map_congr_left
  intro q hq
  have hqbound : q < M.1 := List.mem_range.mp hq
  have heq : nextMember M a.val (List.ofFn fun i => (subsetFin M.1 (sets i)).val) q =
      decide ((⟨q, hqbound⟩ : Fin M.1) ∈
        Lax842588Proofs.Determinization.step (M.toAutomaton alphabet) a sets) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact nextMember_subsetFin_iff alphabet M a sets ⟨q, hqbound⟩
  change (nextMember M a.val
      (List.ofFn fun i => (subsetFin M.1 (sets i)).val) q).toNat = _
  rw [heq]
  simp [hqbound]

theorem determinize_transition_subset (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (a : alphabet.toRankedAlphabet.Symbol)
    (parent : Finset (Fin M.1))
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Finset (Fin M.1)) :
    ((determinize alphabet M).toAutomaton alphabet).transition a
      (subsetFin M.1 parent) (fun i => subsetFin M.1 (children i)) =
      decide (parent = Lax842588Proofs.Determinization.step
        (M.toAutomaton alphabet) a children) := by
  change ((FiniteAutomatonEncoding.encode alphabet (words 2 M.1).length
    (fun a S childSets => decide (S = nextCode M a childSets))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
      _ _ _ = _
  rw [FiniteAutomatonEncoding.transition_encode]
  rw [nextCode_subsetFin]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    ext q
    have hm := congrArg (fun S => subsetMember M.1 S q.val) h
    simpa using hm
  · rintro rfl
    rfl

theorem determinize_accept_subset (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (states : Finset (Fin M.1)) :
    ((determinize alphabet M).toAutomaton alphabet).accept (subsetFin M.1 states) =
      decide (∃ q ∈ states, (M.toAutomaton alphabet).accept q = true) := by
  change ((FiniteAutomatonEncoding.encode alphabet (words 2 M.1).length
    (fun a S childSets => decide (S = nextCode M a childSets))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).accept _ = _
  rw [FiniteAutomatonEncoding.accept_encode]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, hmem, haccept⟩
    have hm : (⟨q, hq⟩ : Fin M.1) ∈ states := by
      change subsetMember M.1 (subsetFin M.1 states).val
        (⟨q, hq⟩ : Fin M.1).val = true at hmem
      rw [subsetMember_subsetFin] at hmem
      exact of_decide_eq_true hmem
    exact ⟨⟨q, hq⟩, hm, by simpa [accepting_eq_accept] using haccept⟩
  · rintro ⟨q, hmem, haccept⟩
    refine ⟨q.val, q.isLt, ?_, ?_⟩
    · rw [subsetMember_subsetFin]
      exact decide_eq_true hmem
    · simpa [accepting_eq_accept] using haccept

theorem determinize_transition_decodes (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (a : alphabet.toRankedAlphabet.Symbol)
    (parent : Fin (determinize alphabet M).1)
    (children : Fin (alphabet.toRankedAlphabet.rank a) →
      Fin (determinize alphabet M).1)
    (hstep : ((determinize alphabet M).toAutomaton alphabet).transition
      a parent children = true) :
    ∃ states : Finset (Fin M.1), parent = subsetFin M.1 states := by
  change ((FiniteAutomatonEncoding.encode alphabet (words 2 M.1).length
    (fun a S childSets => decide (S = nextCode M a childSets))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
      a parent children = true at hstep
  rw [FiniteAutomatonEncoding.transition_encode] at hstep
  have hS := of_decide_eq_true hstep
  let states : Finset (Fin M.1) := Finset.univ.filter fun q =>
    nextMember M a.val (List.ofFn fun i => (children i).val) q.val = true
  refine ⟨states, Fin.ext ?_⟩
  rw [hS]
  unfold nextCode subsetFin encodeSubset
  congr 1
  apply List.map_congr_left
  intro q hq
  have hqbound : q < M.1 := List.mem_range.mp hq
  simp [states, hqbound]

theorem determinize_run_decodes (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (t : Tree alphabet.toRankedAlphabet)
    (code : Fin (determinize alphabet M).1)
    (hrun : ((determinize alphabet M).toAutomaton alphabet).RunsTo t code) :
    ∃ states : Finset (Fin M.1), code = subsetFin M.1 states := by
  cases t with
  | node a children =>
      rcases hrun with ⟨childCodes, hstep, hruns⟩
      exact determinize_transition_decodes alphabet M a code childCodes hstep

theorem determinize_runsTo_subset_iff (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (t : Tree alphabet.toRankedAlphabet)
    (states : Finset (Fin M.1)) :
    ((determinize alphabet M).toAutomaton alphabet).RunsTo t (subsetFin M.1 states) ↔
      (Lax842588Proofs.Determinization.determinize (M.toAutomaton alphabet)).RunsTo t states := by
  classical
  induction t generalizing states with
  | node a children ih =>
      constructor
      · rintro ⟨childCodes, hstep, hruns⟩
        have hdecoded : ∀ i, ∃ childSet : Finset (Fin M.1),
            childCodes i = subsetFin M.1 childSet := by
          intro i
          exact determinize_run_decodes alphabet M (children i) (childCodes i) (hruns i)
        choose childSets hchildCodes using hdecoded
        have hcodes : childCodes = fun i => subsetFin M.1 (childSets i) := by
          funext i
          exact hchildCodes i
        subst childCodes
        refine ⟨childSets, ?_, fun i => (ih i _).mp (hruns i)⟩
        rw [determinize_transition_subset] at hstep
        simpa [Lax842588Proofs.Determinization.determinize] using hstep
      · rintro ⟨childSets, hstep, hruns⟩
        refine ⟨fun i => subsetFin M.1 (childSets i), ?_,
          fun i => (ih i _).mpr (hruns i)⟩
        rw [determinize_transition_subset]
        simpa [Lax842588Proofs.Determinization.determinize] using hstep

theorem determinize_accepts_iff (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ((determinize alphabet M).toAutomaton alphabet).Accepts t ↔
      (M.toAutomaton alphabet).Accepts t := by
  classical
  have habstract := Lax842588Proofs.Determinization.determinize_accepts_iff
    (M.toAutomaton alphabet) t
  constructor
  · rintro ⟨code, haccept, hrun⟩
    obtain ⟨states, rfl⟩ := determinize_run_decodes alphabet M t code hrun
    apply habstract.mp
    refine ⟨states, ?_, (determinize_runsTo_subset_iff alphabet M t states).mp hrun⟩
    rw [determinize_accept_subset] at haccept
    simpa [Lax842588Proofs.Determinization.determinize] using haccept
  · intro hM
    rcases habstract.mpr hM with ⟨states, haccept, hrun⟩
    refine ⟨subsetFin M.1 states, ?_,
      (determinize_runsTo_subset_iff alphabet M t states).mpr hrun⟩
    rw [determinize_accept_subset]
    simpa [Lax842588Proofs.Determinization.determinize] using haccept

theorem determinize_deterministic (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    ((determinize alphabet M).toAutomaton alphabet).Deterministic := by
  intro a children
  let parent : Fin (determinize alphabet M).1 :=
    ⟨nextCode M a.val (List.ofFn fun i => (children i).val), encodeSubset_lt _ _⟩
  refine ⟨parent, ?_, ?_⟩
  · change ((FiniteAutomatonEncoding.encode alphabet (words 2 M.1).length
      (fun a S childSets => decide (S = nextCode M a childSets))
      (fun S => (List.range M.1).any fun q =>
        subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
        a parent children = true
    rw [FiniteAutomatonEncoding.transition_encode]
    simp [parent]
  · intro other hother
    change ((FiniteAutomatonEncoding.encode alphabet (words 2 M.1).length
      (fun a S childSets => decide (S = nextCode M a childSets))
      (fun S => (List.range M.1).any fun q =>
        subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
        a other children = true at hother
    rw [FiniteAutomatonEncoding.transition_encode] at hother
    apply Fin.ext
    simpa [parent] using of_decide_eq_true hother

/-- Complement after the computably numbered powerset construction. -/
def compl (alphabet : RankedAlphabetCode) (M : AutomatonCode) : AutomatonCode :=
  let D := determinize alphabet M
  (D.1, D.2.1, (List.range D.1).filter fun q => !accepting D q)

theorem compl_toAutomaton (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    (compl alphabet M).toAutomaton alphabet =
      Lax842588Proofs.TreeAutomataClosure.flipAccept
        ((determinize alphabet M).toAutomaton alphabet) := by
  unfold compl
  let D := determinize alphabet M
  let body : AutomatonCode := (D.1, D.2.1,
    (List.range D.1).filter fun r => !accepting D r)
  let left := AutomatonCode.toAutomaton alphabet body
  let right := Lax842588Proofs.TreeAutomataClosure.flipAccept (D.toAutomaton alphabet)
  change left = right
  have ht : left.transition = right.transition := by rfl
  have ha : left.accept = right.accept := by
    funext q
    change ((List.range D.1).filter (fun r => !accepting D r)).contains q.val =
      !(D.2.2.contains q.val)
    apply Bool.eq_iff_iff.mpr
    have hq : q.val < D.1 := by simpa [body] using q.isLt
    simp [accepting, hq]
  rcases left with ⟨lt, la⟩
  rcases right with ⟨rt, ra⟩
  exact congrArg₂ Automaton.mk ht ha

theorem compl_accepts_iff (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ((compl alphabet M).toAutomaton alphabet).Accepts t ↔
      ¬ (M.toAutomaton alphabet).Accepts t := by
  rw [compl_toAutomaton]
  exact (Lax842588Proofs.TreeAutomataClosure.flipAccept_accepts_iff_not _
    (determinize_deterministic alphabet M) t).trans
      (not_congr (determinize_accepts_iff alphabet M t))

def union (alphabet : RankedAlphabetCode) (M N : AutomatonCode) : AutomatonCode :=
  compl alphabet (EncodedAutomataOperations.inter alphabet
    (compl alphabet M) (compl alphabet N))

theorem union_accepts_iff (alphabet : RankedAlphabetCode) (M N : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ((union alphabet M N).toAutomaton alphabet).Accepts t ↔
      (M.toAutomaton alphabet).Accepts t ∨ (N.toAutomaton alphabet).Accepts t := by
  rw [union, compl_accepts_iff, EncodedAutomataOperations.inter_accepts_iff,
    compl_accepts_iff, compl_accepts_iff]
  tauto

theorem subsetBits_prim : Primrec fun p : Nat × Nat => subsetBits p.1 p.2 := by
  unfold subsetBits
  exact (Primrec.list_getD ([] : List Nat)).comp
    (words_prim.comp (Primrec.const 2) Primrec.fst) Primrec.snd

theorem subsetMember_prim : Primrec fun p : Nat × Nat × Nat =>
    subsetMember p.1 p.2.1 p.2.2 := by
  unfold subsetMember
  have hbits : Primrec fun p : Nat × Nat × Nat => subsetBits p.1 p.2.1 :=
    subsetBits_prim.comp <| Primrec.pair Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  have hdigit : Primrec fun p : Nat × Nat × Nat =>
      (subsetBits p.1 p.2.1).getD p.2.2 0 :=
    Primrec.list_getD 0 |>.comp hbits (Primrec.snd.comp Primrec.snd)
  exact (Primrec.eq.comp hdigit (Primrec.const 1)).decide

theorem encodeSubset_prim {X : Type*} [Primcodable X]
    (n : X → Nat) (pred : X → Nat → Bool)
    (hn : Primrec n) (hpred : Primrec fun p : X × Nat => pred p.1 p.2) :
    Primrec fun x => encodeSubset (n x) (pred x) := by
  unfold encodeSubset
  have hword : Primrec fun x =>
      (List.range (n x)).map fun q => (pred x q).toNat := by
    apply Primrec.list_map (Primrec.list_range.comp hn)
    exact ((Primrec.dom_bool Bool.toNat).comp hpred).to₂
  have hwords : Primrec fun x => words 2 (n x) :=
    words_prim.comp (Primrec.const 2) hn
  have hbeq : Primrec₂ fun xs ys : List Nat => xs == ys := by
    exact Primrec.eq.decide |>.of_eq fun xs ys => by
      apply Bool.eq_iff_iff.mpr
      simp
  exact Primrec.list_findIdx hwords <|
    hbeq.comp₂ Primrec₂.right (hword.comp Primrec.fst |>.to₂)

theorem childrenAgree_prim : Primrec fun p : Nat × List Nat × List Nat =>
    childrenAgree p.1 p.2.1 p.2.2 := by
  let P := Nat × List Nat × List Nat
  have hlength : Primrec fun p : P => p.2.1.length == p.2.2.length :=
    Primrec.beq.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hrel : PrimrecRel fun (i : Nat) (p : P) =>
      subsetMember p.1 (p.2.1.getD i 0) (p.2.2.getD i 0) = true := by
    have hmember : Primrec fun z : Nat × P =>
        subsetMember z.2.1 (z.2.2.1.getD z.1 0) (z.2.2.2.getD z.1 0) := by
      exact subsetMember_prim.comp <| Primrec.pair
        (Primrec.fst.comp Primrec.snd) <| Primrec.pair
        (Primrec.list_getD 0 |>.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
        (Primrec.list_getD 0 |>.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
    exact (Primrec.eq.comp hmember (Primrec.const true)).primrecRel
  have hall : Primrec fun p : P =>
      (List.range p.2.2.length).all fun i =>
        subsetMember p.1 (p.2.1.getD i 0) (p.2.2.getD i 0) := by
    exact hrel.forall_mem_list.decide.comp
      (Primrec.list_range.comp <|
        Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) Primrec.id
      |>.of_eq fun p => by
        apply Bool.eq_iff_iff.mpr
        simp
  exact Primrec.and.comp hlength hall

theorem nextMember_prim : Primrec fun
    p : AutomatonCode × Nat × List Nat × Nat =>
      nextMember p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let P := AutomatonCode × Nat × List Nat × Nat
  have htest : Primrec fun z : List Nat × P =>
      step z.2.1 z.2.2.1 z.2.2.2.2 z.1 &&
        childrenAgree z.2.1.1 z.2.2.2.1 z.1 := by
    apply Primrec.and.comp
    · exact step_prim.comp <| Primrec.pair (Primrec.fst.comp Primrec.snd) <|
        Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) <|
          Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            Primrec.fst
    · exact childrenAgree_prim.comp <| Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) <|
          Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
            Primrec.fst
  have hrel : PrimrecRel fun (qs : List Nat) (p : P) =>
      (step p.1 p.2.1 p.2.2.2 qs && childrenAgree p.1.1 p.2.2.1 qs) = true :=
    (Primrec.eq.comp htest (Primrec.const true)).primrecRel
  have hlist : Primrec fun p : P => words p.1.1 p.2.2.1.length :=
    words_prim.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_length.comp <|
        Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact hrel.exists_mem_list.decide.comp hlist Primrec.id
    |>.of_eq fun p => by
      apply Bool.eq_iff_iff.mpr
      simp [nextMember]

theorem nextCode_prim : Primrec fun p : AutomatonCode × Nat × List Nat =>
    nextCode p.1 p.2.1 p.2.2 := by
  apply encodeSubset_prim (fun p : AutomatonCode × Nat × List Nat => p.1.1)
    (fun p q => nextMember p.1 p.2.1 p.2.2 q)
  · exact Primrec.fst.comp Primrec.fst
  · exact nextMember_prim.comp <| Primrec.pair
      (Primrec.fst.comp Primrec.fst) <| Primrec.pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) <| Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd

theorem determinize_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (M : X → AutomatonCode)
    (halphabet : Primrec alphabet) (hM : Primrec M) :
    Primrec fun x => determinize (alphabet x) (M x) := by
  let states (x : X) := (words 2 (M x).1).length
  let transition (x : X) (a S : Nat) (children : List Nat) :=
    decide (S = nextCode (M x) a children)
  let accept (x : X) (S : Nat) := (List.range (M x).1).any fun q =>
    subsetMember (M x).1 S q && accepting (M x) q
  change Primrec fun x => FiniteAutomatonEncoding.encode
    (alphabet x) (states x) (transition x) (accept x)
  apply encode_prim alphabet states transition accept halphabet
  · exact Primrec.list_length.comp <|
      words_prim.comp (Primrec.const 2) (Primrec.fst.comp hM)
  · have hnext : Primrec fun p : X × Nat × Nat × List Nat =>
        nextCode (M p.1) p.2.1 p.2.2.2 := by
      exact nextCode_prim.comp <| Primrec.pair (hM.comp Primrec.fst) <|
        Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    exact (Primrec.eq.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hnext).decide
  · let P := X × Nat
    have htest : Primrec fun z : Nat × P =>
        subsetMember (M z.2.1).1 z.2.2 z.1 && accepting (M z.2.1) z.1 := by
      apply Primrec.and.comp
      · exact subsetMember_prim.comp <| Primrec.pair
          (Primrec.fst.comp (hM.comp <| Primrec.fst.comp Primrec.snd)) <|
            Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst
      · exact accepting_prim.comp
          (hM.comp <| Primrec.fst.comp Primrec.snd) Primrec.fst
    have hrel : PrimrecRel fun (q : Nat) (p : P) =>
        (subsetMember (M p.1).1 p.2 q && accepting (M p.1) q) = true :=
      (Primrec.eq.comp htest (Primrec.const true)).primrecRel
    exact hrel.exists_mem_list.decide.comp
        (Primrec.list_range.comp <| Primrec.fst.comp (hM.comp Primrec.fst))
        Primrec.id
      |>.of_eq fun p => by
        apply Bool.eq_iff_iff.mpr
        simp [accept]

theorem compl_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (M : X → AutomatonCode)
    (halphabet : Primrec alphabet) (hM : Primrec M) :
    Primrec fun x => compl (alphabet x) (M x) := by
  have hD : Primrec fun x => determinize (alphabet x) (M x) :=
    determinize_prim alphabet M halphabet hM
  let D (x : X) := determinize (alphabet x) (M x)
  have hrel : PrimrecRel fun (q : Nat) (x : X) => accepting (D x) q = false := by
    exact (Primrec.eq.comp
      (accepting_prim.comp (hD.comp Primrec.snd) Primrec.fst)
      (Primrec.const false)).primrecRel
  have haccept : Primrec fun x =>
      (List.range (D x).1).filter fun q => !accepting (D x) q := by
    exact hrel.listFilter.comp
      (Primrec.list_range.comp <| Primrec.fst.comp hD) Primrec.id
      |>.of_eq fun x => by
        apply List.filter_congr
        intro q hq
        simp
  unfold compl
  exact Primrec.pair (Primrec.fst.comp hD) <| Primrec.pair
    (Primrec.fst.comp (Primrec.snd.comp hD)) haccept

theorem union_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode)
    (M N : X → AutomatonCode)
    (halphabet : Primrec alphabet) (hM : Primrec M) (hN : Primrec N) :
    Primrec fun x => union (alphabet x) (M x) (N x) := by
  have hMc : Primrec fun x => compl (alphabet x) (M x) :=
    compl_prim alphabet M halphabet hM
  have hNc : Primrec fun x => compl (alphabet x) (N x) :=
    compl_prim alphabet N halphabet hN
  have hinter : Primrec fun x => EncodedAutomataOperations.inter
      (alphabet x) (compl (alphabet x) (M x)) (compl (alphabet x) (N x)) :=
    inter_prim.comp <| Primrec.pair halphabet (Primrec.pair hMc hNc)
  unfold union
  exact compl_prim alphabet
    (fun x => EncodedAutomataOperations.inter (alphabet x)
      (compl (alphabet x) (M x)) (compl (alphabet x) (N x)))
    halphabet hinter

end Lax842588Proofs.EncodedComputableDeterminization
