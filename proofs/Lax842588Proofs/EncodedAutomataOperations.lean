import Mathlib.Logic.Equiv.Fin.Basic
import Lax842588Proofs.FiniteAutomatonEncoding
import Lax842588Proofs.EncodedAutomatonEvaluation
import Lax842588Proofs.TreeAutomataClosure
import Lax842588Proofs.Determinization

namespace Lax842588Proofs.EncodedAutomataOperations

open Lax842588.ValueTranslations
open Lax842588.RankedTree
open Lax842588.TreeAutomaton
open Lax842588Proofs.FiniteAutomatonEncoding

def rename {A : RankedAlphabet} {Q R : Type*} (e : Q ≃ R)
    (M : Automaton A Q) : Automaton A R where
  transition a r children := M.transition a (e.symm r) (fun i => e.symm (children i))
  accept r := M.accept (e.symm r)

theorem rename_runsTo_iff {A : RankedAlphabet} {Q R : Type*} (e : Q ≃ R)
    (M : Automaton A Q) (t : Tree A) (r : R) :
    (rename e M).RunsTo t r ↔ M.RunsTo t (e.symm r) := by
  induction t generalizing r with
  | node a children ih =>
      constructor
      · rintro ⟨rs, hstep, hruns⟩
        exact ⟨fun i => e.symm (rs i), hstep, fun i => (ih i _).mp (hruns i)⟩
      · rintro ⟨qs, hstep, hruns⟩
        refine ⟨fun i => e (qs i), ?_, fun i => (ih i _).mpr ?_⟩
        · simpa [rename]
        · simpa using hruns i

theorem rename_accepts_iff {A : RankedAlphabet} {Q R : Type*} (e : Q ≃ R)
    (M : Automaton A Q) (t : Tree A) :
    (rename e M).Accepts t ↔ M.Accepts t := by
  constructor
  · rintro ⟨r, hr, hrun⟩
    exact ⟨e.symm r, hr, (rename_runsTo_iff e M t r).mp hrun⟩
  · rintro ⟨q, hq, hrun⟩
    exact ⟨e q, by simpa [rename], (rename_runsTo_iff e M t (e q)).mpr (by simpa using hrun)⟩

/-- Boolean transition-table lookup in an encoded automaton. -/
def step (M : AutomatonCode) (a q : Nat) (children : List Nat) : Bool :=
  M.2.1.any fun tr => decide (tr = (a, q, children))

def accepting (M : AutomatonCode) (q : Nat) : Bool := M.2.2.contains q

theorem step_eq_transition (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (a : alphabet.toRankedAlphabet.Symbol) (q : Fin M.1)
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Fin M.1) :
    step M a.val q.val (List.ofFn fun i => (children i).val) =
      (M.toAutomaton alphabet).transition a q children := by
  simp only [step, AutomatonCode.toAutomaton]
  congr 1
  funext tr
  rw [decide_eq_decide]
  exact Prod.ext_iff.trans (and_congr Iff.rfl
    (Prod.ext_iff.trans (and_congr Iff.rfl Iff.rfl)))

theorem accepting_eq_accept (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (q : Fin M.1) : accepting M q.val = (M.toAutomaton alphabet).accept q := rfl

/-- Synchronous intersection, with pair `(q,r)` numbered `q * |R| + r`. -/
def inter (alphabet : RankedAlphabetCode) (M N : AutomatonCode) : AutomatonCode :=
  encode alphabet (M.1 * N.1)
    (fun a qr children =>
      step M a (qr / N.1) (children.map fun s => s / N.1) &&
      step N a (qr % N.1) (children.map fun s => s % N.1))
    (fun qr => accepting M (qr / N.1) && accepting N (qr % N.1))

theorem inter_toAutomaton (alphabet : RankedAlphabetCode) (M N : AutomatonCode) :
    (inter alphabet M N).toAutomaton alphabet =
      rename finProdFinEquiv
        (Lax842588Proofs.TreeAutomataClosure.product
          (M.toAutomaton alphabet) (N.toAutomaton alphabet)) := by
  change (encode alphabet (M.1 * N.1)
      (fun a qr children =>
        step M a (qr / N.1) (children.map fun s => s / N.1) &&
        step N a (qr % N.1) (children.map fun s => s % N.1))
      (fun qr => accepting M (qr / N.1) && accepting N (qr % N.1))).toAutomaton alphabet = _
  rw [FiniteAutomatonEncoding.toAutomaton_encode]
  congr
  · funext a qr children
    simp only [rename, Lax842588Proofs.TreeAutomataClosure.product,
      finProdFinEquiv_symm_apply, List.map_ofFn]
    have hM := step_eq_transition alphabet M a qr.divNat
      (fun i => (children i).divNat)
    have hN := step_eq_transition alphabet N a qr.modNat
      (fun i => (children i).modNat)
    rw [← hM, ← hN]
    rfl

theorem inter_accepts_iff (alphabet : RankedAlphabetCode) (M N : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ((inter alphabet M N).toAutomaton alphabet).Accepts t ↔
      (M.toAutomaton alphabet).Accepts t ∧ (N.toAutomaton alphabet).Accepts t := by
  rw [inter_toAutomaton]
  exact (rename_accepts_iff _ _ _).trans
    (Lax842588Proofs.TreeAutomataClosure.product_accepts_iff _ _ _)

/-- Every subset of the canonical `n`-element state type, obtained from its
Boolean characteristic word. -/
def allSubsets (n : Nat) : List (Finset (Fin n)) :=
  (FiniteAutomatonEncoding.words 2 n).map fun bits =>
    Finset.univ.filter fun q => bits.getD q.val 0 = 1

/-- A strict upper bound for the canonical numeric encodings of all subsets. -/
def subsetStateBound (n : Nat) : Nat :=
  ((allSubsets n).map Encodable.encode).foldl max 0 + 1

def decodeSubset (n q : Nat) : Option (Finset (Fin n)) := Encodable.decode q

def subsetMember (n S q : Nat) : Bool :=
  match decodeSubset n S with
  | some states => if h : q < n then decide (⟨q, h⟩ ∈ states) else false
  | none => false

theorem decodeSubset_encode {n : Nat} (s : Finset (Fin n)) :
    decodeSubset n (Encodable.encode s) = some s := by
  simp [decodeSubset]

theorem subsetMember_encode {n : Nat} (s : Finset (Fin n)) (q : Fin n) :
    subsetMember n (Encodable.encode s) q.val = decide (q ∈ s) := by
  simp [subsetMember, decodeSubset_encode, q.isLt]

def nextSubset (M : AutomatonCode) (a : Nat) (childSets : List Nat) :
    Finset (Fin M.1) :=
  Finset.univ.filter fun q =>
    (FiniteAutomatonEncoding.words M.1 childSets.length).any fun qs =>
      step M a q.val qs &&
        List.all (List.zipWith (subsetMember M.1) childSets qs) id

theorem all_zipWith_subsetMember_encode {n k : Nat}
    (sets : Fin k → Finset (Fin n)) (qs : List Nat) (hlen : qs.length = k)
    (hbound : ∀ q ∈ qs, q < n) :
    List.all (List.zipWith (subsetMember n)
      (List.ofFn fun i => Encodable.encode (sets i)) qs) id = true ↔
      ∀ i : Fin k, ⟨qs.get ⟨i.val, by omega⟩,
        hbound _ (List.get_mem _ _)⟩ ∈ sets i := by
  have hlength : (List.ofFn fun i => Encodable.encode (sets i)).length = qs.length := by simp [hlen]
  simp only [List.all_eq_true, id_eq]
  rw [List.forall_mem_iff_get]
  constructor
  · intro h i
    have hz := h ⟨i.val, by simp [List.length_zipWith, hlen]⟩
    rw [List.get_eq_getElem] at hz
    simp only [List.getElem_zipWith, List.getElem_ofFn] at hz
    have hb := hbound qs[i.val] (List.getElem_mem _)
    simp [subsetMember, decodeSubset, hb] at hz
    simpa using hz
  · intro h i
    have hi : i.val < k := by simpa [List.length_zipWith, hlen] using i.isLt
    rw [List.get_eq_getElem]
    simp only [List.getElem_zipWith, List.getElem_ofFn]
    have hb := hbound qs[i.val] (List.getElem_mem _)
    simp [subsetMember, decodeSubset, hb]
    simpa using h ⟨i.val, hi⟩

theorem all_zipWith_subsetMember_encode_iff {n k : Nat}
    (sets : Fin k → Finset (Fin n)) (qs : List Nat)
    (hqs : qs ∈ FiniteAutomatonEncoding.words n k) :
    List.all (List.zipWith (subsetMember n)
      (List.ofFn fun i => Encodable.encode (sets i)) qs) id = true ↔
      ∀ i : Fin k, (⟨qs.get ⟨i.val, by
        have hlen := (FiniteAutomatonEncoding.mem_words_iff.mp hqs).1
        omega⟩, by
          exact (FiniteAutomatonEncoding.mem_words_iff.mp hqs).2 _
            (List.get_mem _ _)⟩ : Fin n) ∈ sets i := by
  have hlen := (FiniteAutomatonEncoding.mem_words_iff.mp hqs).1
  exact all_zipWith_subsetMember_encode sets qs hlen
    (FiniteAutomatonEncoding.mem_words_iff.mp hqs).2

theorem nextSubset_encode (alphabet : RankedAlphabetCode) (M : AutomatonCode)
    (a : alphabet.toRankedAlphabet.Symbol)
    (childSets : Fin (alphabet.toRankedAlphabet.rank a) → Finset (Fin M.1)) :
    nextSubset M a.val (List.ofFn fun i => Encodable.encode (childSets i)) =
      Lax842588Proofs.Determinization.step (M.toAutomaton alphabet) a childSets := by
  classical
  ext q
  simp only [nextSubset, Finset.mem_filter, Finset.mem_univ, true_and,
    Lax842588Proofs.Determinization.mem_step, List.any_eq_true]
  constructor
  · rintro ⟨qs, hqs, hand⟩
    have ⟨hstep, hall⟩ := Bool.and_eq_true_iff.mp hand
    have hqsRank : qs ∈ FiniteAutomatonEncoding.words M.1
        (alphabet.toRankedAlphabet.rank a) := by simpa using hqs
    have hlen := (FiniteAutomatonEncoding.mem_words_iff.mp hqsRank).1
    have hbound := (FiniteAutomatonEncoding.mem_words_iff.mp hqs).2
    let states : Fin (alphabet.toRankedAlphabet.rank a) → Fin M.1 := fun i =>
      ⟨qs.get ⟨i.val, by omega⟩,
        hbound _ (List.get_mem _ _)⟩
    refine ⟨states, ?_, ?_⟩
    · rw [← step_eq_transition alphabet M a q states]
      have heq : List.ofFn (fun i => (states i).val) = qs := by
        apply List.ext_get
        · simp [hlen]
        · intro i hi₁ hi₂
          simp [states]
      rw [heq]
      exact hstep
    · exact (all_zipWith_subsetMember_encode_iff childSets qs hqsRank).mp hall
  · rintro ⟨states, hstep, hchildren⟩
    let qs := List.ofFn fun i => (states i).val
    have hqs : qs ∈ FiniteAutomatonEncoding.words M.1
        (alphabet.toRankedAlphabet.rank a) :=
      FiniteAutomatonEncoding.ofFn_mem_words states
    have hqs' : qs ∈ FiniteAutomatonEncoding.words M.1
        (List.ofFn fun i => Encodable.encode (childSets i)).length := by
      simpa using hqs
    refine ⟨qs, hqs', Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩⟩
    · rw [step_eq_transition alphabet M a q states]
      simpa [qs] using hstep
    · apply (all_zipWith_subsetMember_encode_iff childSets qs hqs).mpr
      intro i
      simpa [qs] using hchildren i

theorem encode_subset_lt (n : Nat) (s : Finset (Fin n)) :
    Encodable.encode s < subsetStateBound n := by
  unfold subsetStateBound
  have hs : s ∈ allSubsets n := by
    unfold allSubsets
    let bits := List.ofFn fun q : Fin n => if q ∈ s then 1 else 0
    refine List.mem_map.mpr ⟨bits, ?_, ?_⟩
    · rw [FiniteAutomatonEncoding.mem_words_iff]
      exact ⟨by simp [bits], fun b hb => by
        obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hb
        by_cases hq : q ∈ s <;> simp [bits, hq]⟩
    · ext q
      simp [bits, List.getD_eq_getElem?_getD]
  have hmem : Encodable.encode s ∈ (allSubsets n).map Encodable.encode :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  have foldl_max_ge {xs : List Nat} {x init : Nat} (hx : x ∈ xs) :
      x ≤ xs.foldl max init := by
    have hinit : ∀ (ys : List Nat) (a : Nat), a ≤ ys.foldl max a := by
      intro ys
      induction ys with
      | nil => simp
      | cons z zs ih =>
          intro a
          simp only [List.foldl_cons]
          exact le_trans (le_max_left _ _) (ih (max a z))
    induction xs generalizing init with
    | nil => simp at hx
    | cons y ys ih =>
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [List.foldl_cons]
          exact le_trans (le_max_right init x) (hinit ys (max init x))
        · simpa only [List.foldl_cons] using ih (init := max init y) hx
  have hle : Encodable.encode s ≤
      ((allSubsets n).map Encodable.encode).foldl max 0 := foldl_max_ge hmem
  omega

/-- Powerset determinization using mathlib's canonical encoding of finite
sets. State numbers that do not decode to a subset have no transitions. -/
def determinize (alphabet : RankedAlphabetCode) (M : AutomatonCode) : AutomatonCode :=
  encode alphabet (subsetStateBound M.1)
    (fun a S childSets => decide (S = Encodable.encode (nextSubset M a childSets)))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)

def subsetFin (n : Nat) (s : Finset (Fin n)) : Fin (subsetStateBound n) :=
  ⟨Encodable.encode s, encode_subset_lt n s⟩

theorem determinize_transition_subset (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (a : alphabet.toRankedAlphabet.Symbol)
    (parent : Finset (Fin M.1))
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Finset (Fin M.1)) :
    ((determinize alphabet M).toAutomaton alphabet).transition a
      (subsetFin M.1 parent) (fun i => subsetFin M.1 (children i)) =
      decide (parent = Lax842588Proofs.Determinization.step
        (M.toAutomaton alphabet) a children) := by
  change ((encode alphabet (subsetStateBound M.1)
    (fun a S childSets => decide (S = Encodable.encode (nextSubset M a childSets)))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition _ _ _ = _
  rw [FiniteAutomatonEncoding.transition_encode]
  simp only [subsetFin]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [Encodable.encode_injective.eq_iff]
  rw [nextSubset_encode]

theorem determinize_accept_subset (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (states : Finset (Fin M.1)) :
    ((determinize alphabet M).toAutomaton alphabet).accept (subsetFin M.1 states) =
      decide (∃ q ∈ states, (M.toAutomaton alphabet).accept q = true) := by
  change ((encode alphabet (subsetStateBound M.1)
    (fun a S childSets => decide (S = Encodable.encode (nextSubset M a childSets)))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).accept _ = _
  rw [FiniteAutomatonEncoding.accept_encode]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true,
    subsetFin, subsetMember_encode, decide_eq_true_eq, accepting_eq_accept]
  constructor
  · rintro ⟨q, hq, hmem, haccept⟩
    have hm : (⟨q, hq⟩ : Fin M.1) ∈ states := by
      simpa [subsetMember, decodeSubset, hq] using hmem
    exact ⟨⟨q, hq⟩, hm, by simpa [accepting_eq_accept] using haccept⟩
  · rintro ⟨q, hmem, haccept⟩
    refine ⟨q.val, q.isLt, ?_, ?_⟩
    · simpa [subsetMember, decodeSubset, q.isLt] using hmem
    · simpa [accepting_eq_accept] using haccept

theorem determinize_transition_decodes (alphabet : RankedAlphabetCode)
    (M : AutomatonCode) (a : alphabet.toRankedAlphabet.Symbol)
    (parent : Fin (determinize alphabet M).1)
    (children : Fin (alphabet.toRankedAlphabet.rank a) →
      Fin (determinize alphabet M).1)
    (hstep : ((determinize alphabet M).toAutomaton alphabet).transition
      a parent children = true) :
    ∃ states : Finset (Fin M.1), parent = subsetFin M.1 states := by
  change ((encode alphabet (subsetStateBound M.1)
    (fun a S childSets => decide (S = Encodable.encode (nextSubset M a childSets)))
    (fun S => (List.range M.1).any fun q =>
      subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
      a parent children = true at hstep
  rw [FiniteAutomatonEncoding.transition_encode] at hstep
  have hS := of_decide_eq_true hstep
  let S := nextSubset M a.val (List.ofFn fun i => (children i).val)
  refine ⟨S, Fin.ext ?_⟩
  exact hS

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
        refine ⟨fun i => subsetFin M.1 (childSets i), ?_, fun i => (ih i _).mpr (hruns i)⟩
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
    have hdecoded := determinize_run_decodes alphabet M t code hrun
    obtain ⟨states, rfl⟩ := hdecoded
    apply habstract.mp
    refine ⟨states, ?_, (determinize_runsTo_subset_iff alphabet M t states).mp hrun⟩
    rw [determinize_accept_subset] at haccept
    simpa [Lax842588Proofs.Determinization.determinize] using haccept
  · intro hM
    have hdet := habstract.mpr hM
    rcases hdet with ⟨states, haccept, hrun⟩
    refine ⟨subsetFin M.1 states, ?_,
      (determinize_runsTo_subset_iff alphabet M t states).mpr hrun⟩
    rw [determinize_accept_subset]
    simpa [Lax842588Proofs.Determinization.determinize] using haccept

theorem determinize_deterministic (alphabet : RankedAlphabetCode) (M : AutomatonCode) :
    ((determinize alphabet M).toAutomaton alphabet).Deterministic := by
  intro a children
  let states := nextSubset M a.val (List.ofFn fun i => (children i).val)
  have hbound : Encodable.encode states < subsetStateBound M.1 :=
    encode_subset_lt M.1 states
  let parent : Fin (determinize alphabet M).1 := ⟨Encodable.encode states, hbound⟩
  refine ⟨parent, ?_, ?_⟩
  · change ((encode alphabet (subsetStateBound M.1)
      (fun a S childSets => decide (S = Encodable.encode (nextSubset M a childSets)))
      (fun S => (List.range M.1).any fun q =>
        subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
        a parent children = true
    rw [FiniteAutomatonEncoding.transition_encode]
    simp [parent, states]
  · intro other hother
    change ((encode alphabet (subsetStateBound M.1)
      (fun a S childSets => decide (S = Encodable.encode (nextSubset M a childSets)))
      (fun S => (List.range M.1).any fun q =>
        subsetMember M.1 S q && accepting M q)).toAutomaton alphabet).transition
        a other children = true at hother
    rw [FiniteAutomatonEncoding.transition_encode] at hother
    apply Fin.ext
    simpa [parent, states] using of_decide_eq_true hother

/-- Complement after determinization. -/
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
    (List.range D.1).filter (fun r => !accepting D r))
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
  compl alphabet (inter alphabet (compl alphabet M) (compl alphabet N))

theorem union_accepts_iff (alphabet : RankedAlphabetCode) (M N : AutomatonCode)
    (t : Tree alphabet.toRankedAlphabet) :
    ((union alphabet M N).toAutomaton alphabet).Accepts t ↔
      (M.toAutomaton alphabet).Accepts t ∨ (N.toAutomaton alphabet).Accepts t := by
  rw [union, compl_accepts_iff, inter_accepts_iff,
    compl_accepts_iff, compl_accepts_iff]
  tauto

/-- Existential projection along a surjection of finite numbered alphabets.
`sourceOf target` lists all source symbols over the target symbol. -/
def project (targetAlphabet : RankedAlphabetCode) (sourceOf : Nat → List Nat)
    (M : AutomatonCode) : AutomatonCode :=
  encode targetAlphabet M.1
    (fun a q children => (sourceOf a).any fun source => step M source q children)
    (accepting M)

/-- Pull an automaton back along a map from source symbols to target symbols. -/
def pullback (sourceAlphabet : RankedAlphabetCode) (symbolMap : Nat → Nat)
    (M : AutomatonCode) : AutomatonCode :=
  encode sourceAlphabet M.1
    (fun a q children => step M (symbolMap a) q children) (accepting M)

end Lax842588Proofs.EncodedAutomataOperations
