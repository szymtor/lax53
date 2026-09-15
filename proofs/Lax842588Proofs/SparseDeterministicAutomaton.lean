import Lax842588Proofs.EncodedAutomataOperations
import Lax842588Proofs.FiniteAutomatonEncoding

/-!
Sparse row-order presentations of deterministic tree automata.

The generic mathematical encoder enumerates every candidate parent state and
filters the transition relation.  When the parent is a function of the symbol
and child row, an implementation can instead emit exactly one record per row.
This module proves that the smaller, directly generable code has the same
automaton semantics.
-/

set_option backward.isDefEq.respectTransparency false

namespace Lax842588Proofs.SparseDeterministicAutomaton

open Lax842588.ValueTranslations
open Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.EncodedAutomataOperations
open Lax842588Proofs.FiniteAutomatonEncoding

def code (alphabet : RankedAlphabetCode) (states : Nat)
    (parent : Nat → List Nat → Nat) (accept : Nat → Bool) :
    AutomatonCode :=
  (states,
    (List.range alphabet.length).flatMap fun a =>
      (List.range (states ^ alphabet.getD a 0)).map fun row =>
        let children := radixWord states (alphabet.getD a 0) row
        (a, parent a children, children),
    (List.range states).filter accept)

theorem step_code (alphabet : RankedAlphabetCode) (states : Nat)
    (parent : Nat → List Nat → Nat) (accept : Nat → Bool)
    (a q : Nat) (children : List Nat)
    (ha : a < alphabet.length)
    (hchildren : children ∈ words states (alphabet.getD a 0)) :
    step (code alphabet states parent accept) a q children =
      decide (q = parent a children) := by
  apply Bool.eq_iff_iff.mpr
  simp only [step, code, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨transition, htransition, rfl⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map] at htransition
    obtain ⟨a', _, row, hrow, heq⟩ := htransition
    rcases Prod.ext_iff.mp heq with ⟨haeq, hrest⟩
    change a' = a at haeq
    subst a'
    rcases Prod.ext_iff.mp hrest with ⟨hq, hchildrenEq⟩
    change parent a (radixWord states (alphabet.getD a 0) row) = q at hq
    change radixWord states (alphabet.getD a 0) row = children at hchildrenEq
    rw [hchildrenEq] at hq
    exact hq.symm
  · intro hq
    let row := (words states (alphabet.getD a 0)).idxOf children
    have hrowWords : row < (words states (alphabet.getD a 0)).length :=
      List.idxOf_lt_length_iff.mpr hchildren
    have hrow : row < states ^ alphabet.getD a 0 := by
      simpa [words_length] using hrowWords
    have hchildrenEq :
        radixWord states (alphabet.getD a 0) row = children := by
      rw [← words_getD_eq_radixWord states _ row hrow]
      rw [List.getD_eq_getElem (l := words states (alphabet.getD a 0))
        (d := []) hrowWords]
      exact List.idxOf_get hrowWords
    refine ⟨(a, q, children), ?_, rfl⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map]
    refine ⟨a, ha, row, hrow, ?_⟩
    change (a, parent a (radixWord states (alphabet.getD a 0) row),
      radixWord states (alphabet.getD a 0) row) = (a, q, children)
    rw [hchildrenEq, ← hq]

theorem transition_code (alphabet : RankedAlphabetCode) (states : Nat)
    (parent : Nat → List Nat → Nat) (accept : Nat → Bool)
    (a : alphabet.toRankedAlphabet.Symbol) (q : Fin states)
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Fin states) :
    ((code alphabet states parent accept).toAutomaton alphabet).transition
        a q children =
      decide (q.val = parent a.val
        (List.ofFn fun i => (children i).val)) := by
  rw [← step_eq_transition]
  apply step_code
  · exact a.isLt
  · have hrank : alphabet.getD a.val 0 = alphabet.get a := by
      simp [List.getD_eq_getElem?_getD, a.isLt]
    rw [hrank]
    exact ofFn_mem_words children

@[simp] theorem accept_code (alphabet : RankedAlphabetCode) (states : Nat)
    (parent : Nat → List Nat → Nat) (accept : Nat → Bool)
    (q : Fin states) :
    ((code alphabet states parent accept).toAutomaton alphabet).accept q =
      accept q.val := by
  simp [code, AutomatonCode.toAutomaton]

/-- Sparse row order and the generic complete enumerator define the same
automaton when the latter relation merely tests the uniquely computed parent.
-/
theorem toAutomaton_code_eq_encode
    (alphabet : RankedAlphabetCode) (states : Nat)
    (parent : Nat → List Nat → Nat) (accept : Nat → Bool) :
    (code alphabet states parent accept).toAutomaton alphabet =
      (FiniteAutomatonEncoding.encode alphabet states
        (fun a q children => decide (q = parent a children)) accept).toAutomaton
        alphabet := by
  let left := (code alphabet states parent accept).toAutomaton alphabet
  let right :=
    (FiniteAutomatonEncoding.encode alphabet states
      (fun a q children => decide (q = parent a children)) accept).toAutomaton
      alphabet
  change left = right
  have ht : left.transition = right.transition := by
    funext a q children
    change
      ((code alphabet states parent accept).toAutomaton alphabet).transition
          a q children =
        ((FiniteAutomatonEncoding.encode alphabet states
          (fun a q children => decide (q = parent a children)) accept).toAutomaton
          alphabet).transition a q children
    rw [transition_code, FiniteAutomatonEncoding.transition_encode]
  have ha : left.accept = right.accept := by
    funext q
    change
      ((code alphabet states parent accept).toAutomaton alphabet).accept q =
        ((FiniteAutomatonEncoding.encode alphabet states
          (fun a q children => decide (q = parent a children)) accept).toAutomaton
          alphabet).accept q
    rw [accept_code, FiniteAutomatonEncoding.accept_encode]
  rcases left with ⟨lt, la⟩
  rcases right with ⟨rt, ra⟩
  exact congrArg₂ Lax842588.TreeAutomaton.Automaton.mk ht ha

end Lax842588Proofs.SparseDeterministicAutomaton
