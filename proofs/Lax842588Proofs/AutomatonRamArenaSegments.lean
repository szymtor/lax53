import Mathlib.Data.List.GetD

/-!
Pointwise table-segment predicates used by the charged structural frontend.
They let loop proofs account for one in-place store at a time without ever
treating equality of a whole runtime array as a unit-cost operation.
-/

namespace Lax842588Proofs.AutomatonRamArenaSegments

/-- `words` occurs in `parameter` beginning at `start`. -/
def WordsAt (parameter : List Nat) (start : Nat) (words : List Nat) : Prop :=
  ∀ i < words.length,
    parameter.getD (start + i) 0 = words.getD i 0

/-- Two arrays agree below a boundary. -/
def SameBefore (parameter original : List Nat) (limit : Nat) : Prop :=
  ∀ i < limit, parameter.getD i 0 = original.getD i 0

theorem wordsAt_nil (parameter : List Nat) (start : Nat) :
    WordsAt parameter start [] := by
  simp [WordsAt]

theorem sameBefore_refl (parameter : List Nat) (limit : Nat) :
    SameBefore parameter parameter limit := by
  simp [SameBefore]

theorem sameBefore_trans {first second third : List Nat} {limit : Nat}
    (hfirst : SameBefore first second limit)
    (hsecond : SameBefore second third limit) :
    SameBefore first third limit := by
  intro i hi
  exact (hfirst i hi).trans (hsecond i hi)

theorem wordsAt_of_sameBefore {parameter original words : List Nat}
    {start limit : Nat}
    (hsame : SameBefore parameter original limit)
    (hwords : WordsAt original start words)
    (hend : start + words.length ≤ limit) :
    WordsAt parameter start words := by
  intro i hi
  exact (hsame (start + i) (by omega)).trans (hwords i hi)

theorem sameBefore_set_after {parameter original : List Nat}
    {limit index value : Nat}
    (hsame : SameBefore parameter original limit)
    (hafter : limit ≤ index) (hindex : index < parameter.length) :
    SameBefore (parameter.set index value) original limit := by
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getElem_set_ne (by omega)]
  rw [← List.getD_eq_getElem parameter 0 (by omega)]
  exact hsame i hi

theorem wordsAt_set_append {parameter words : List Nat} {start value : Nat}
    (hwords : WordsAt parameter start words)
    (hslot : start + words.length < parameter.length) :
    WordsAt (parameter.set (start + words.length) value)
      start (words ++ [value]) := by
  intro i hi
  by_cases hold : i < words.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega)]
    rw [List.getElem_set_ne (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    rw [List.getElem_append_left hold]
    rw [← List.getD_eq_getElem parameter 0 (by omega)]
    rw [← List.getD_eq_getElem words 0 hold]
    exact hwords i hold
  · have hiEq : i = words.length := by simp at hi; omega
    subst i
    rw [List.getD_eq_getElem _ _ (by simp; simpa using hslot)]
    rw [List.getElem_set_self (by simp; simpa using hslot)]
    simp

theorem wordsAt_set_singleton {parameter : List Nat} {start value : Nat}
    (hstart : start < parameter.length) :
    WordsAt (parameter.set start value) start [value] := by
  simpa using wordsAt_set_append (value := value)
    (wordsAt_nil parameter start) (by simpa using hstart)

theorem wordsAt_set_before {parameter words : List Nat}
    {start index value : Nat}
    (hwords : WordsAt parameter start words)
    (hspace : start + words.length ≤ parameter.length)
    (hbefore : index < start) :
    WordsAt (parameter.set index value) start words := by
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  rw [List.getElem_set_ne (by omega)]
  rw [← List.getD_eq_getElem parameter 0 (by omega)]
  exact hwords i hi

theorem wordsAt_append {parameter xs ys : List Nat} {start : Nat}
    (hxs : WordsAt parameter start xs)
    (hys : WordsAt parameter (start + xs.length) ys) :
    WordsAt parameter start (xs ++ ys) := by
  intro i hi
  by_cases hleft : i < xs.length
  · rw [List.getD_append]
    · exact hxs i hleft
    · exact hleft
  · rw [List.getD_append_right xs ys 0 i (by omega)]
    rw [show start + i = start + xs.length + (i - xs.length) by omega]
    apply hys (i - xs.length)
    simp only [List.length_append] at hi
    omega

theorem wordsAt_append_right {parameter xs ys : List Nat} {start : Nat}
    (hwords : WordsAt parameter start (xs ++ ys)) :
    WordsAt parameter (start + xs.length) ys := by
  intro i hi
  have hall := hwords (xs.length + i) (by simp; omega)
  rw [List.getD_append_right xs ys 0 (xs.length + i) (by omega)] at hall
  simpa [Nat.add_assoc] using hall

theorem wordsAt_take {parameter words : List Nat} {start count : Nat}
    (hwords : WordsAt parameter start words) :
    WordsAt parameter start (words.take count) := by
  intro i hi
  have hiWords : i < words.length := by
    have := List.length_take_le' count words
    omega
  rw [List.getD_eq_getElem _ _ hi]
  rw [List.getElem_take]
  rw [← List.getD_eq_getElem words 0 hiWords]
  exact hwords i hiWords

end Lax842588Proofs.AutomatonRamArenaSegments
