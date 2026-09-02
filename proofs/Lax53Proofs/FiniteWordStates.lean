import Mathlib.Data.List.Nodup
import Lax53Proofs.FiniteAutomatonEncoding

namespace Lax53Proofs.FiniteWordStates

open Lax53Proofs.FiniteAutomatonEncoding

/-- Canonical finite states represented by words of a fixed length over a
numbered finite alphabet. -/
abbrev WordState (base length : Nat) := Fin (words base length).length

theorem words_nodup (base length : Nat) : (words base length).Nodup := by
  induction length with
  | zero => simp [words]
  | succ length ih =>
      simp only [words]
      apply List.nodup_flatMap.mpr
      constructor
      · intro a ha
        exact ih.map (fun _ _ h => List.cons.inj h |>.2)
      · apply (List.nodup_range : (List.range base).Nodup).pairwise_of_forall_ne
        intro a ha b hb hab
        change List.Disjoint _ _
        rw [List.disjoint_left]
        intro z hza hzb
        obtain ⟨xs, -, rfl⟩ := List.mem_map.mp hza
        obtain ⟨ys, -, h⟩ := List.mem_map.mp hzb
        exact hab (List.cons.inj h).1.symm

/-- Read the digit word represented by a canonical state number. -/
def decode (base length : Nat) (q : WordState base length) : List Nat :=
  (words base length).get q

theorem decode_mem (base length : Nat) (q : WordState base length) :
    decode base length q ∈ words base length := List.get_mem _ _

theorem decode_length (base length : Nat) (q : WordState base length) :
    (decode base length q).length = length :=
  (mem_words_iff.mp (decode_mem base length q)).1

theorem decode_get_lt (base length : Nat) (q : WordState base length)
    (i : Fin length) :
    (decode base length q).get ⟨i.val, by simpa [decode_length]⟩ < base :=
  (mem_words_iff.mp (decode_mem base length q)).2 _ (List.get_mem _ _)

/-- Number a bounded word by its index in the canonical enumeration. -/
def encode (base length : Nat) (f : Fin length → Fin base) :
    WordState base length :=
  ⟨(words base length).idxOf (List.ofFn fun i => (f i).val), by
    apply List.idxOf_lt_length_iff.mpr
    exact ofFn_mem_words f⟩

theorem decode_encode (base length : Nat) (f : Fin length → Fin base) :
    decode base length (encode base length f) = List.ofFn fun i => (f i).val := by
  unfold decode encode
  exact List.idxOf_get (List.idxOf_lt_length_of_mem (ofFn_mem_words f))

/-- The bounded function represented by a canonical word state. -/
def toFun (base length : Nat) (q : WordState base length) : Fin length → Fin base :=
  fun i => ⟨(decode base length q).get
    ⟨i.val, by simpa [decode_length]⟩, decode_get_lt base length q i⟩

theorem toFun_encode (base length : Nat) (f : Fin length → Fin base) :
    toFun base length (encode base length f) = f := by
  funext i
  apply Fin.ext
  simp [toFun, decode_encode]

theorem encode_toFun (base length : Nat) (q : WordState base length) :
    encode base length (toFun base length q) = q := by
  apply Fin.ext
  simp only [encode]
  rw [show List.ofFn (fun i => ((toFun base length q) i).val) =
      decode base length q by
    apply List.ext_get
    · simp [decode_length]
    · intro i h₁ h₂
      simp [toFun]]
  have hidx : (words base length).idxOf (decode base length q) = q.val := by
    exact congrArg Fin.val ((words_nodup base length).get_inj_iff.mp
      (show (words base length).get
          ⟨(words base length).idxOf (decode base length q),
            List.idxOf_lt_length_iff.mpr (decode_mem base length q)⟩ =
        (words base length).get q by
        rw [List.idxOf_get (List.idxOf_lt_length_of_mem
          (decode_mem base length q))]
        rfl))
  exact hidx

def wordStateEquiv (base length : Nat) :
    WordState base length ≃ (Fin length → Fin base) where
  toFun := toFun base length
  invFun := encode base length
  left_inv := encode_toFun base length
  right_inv := toFun_encode base length

/-- The canonical numbering of Booleans used in binary word states. -/
def boolFin : Bool ≃ Fin 2 where
  toFun
    | false => 0
    | true => 1
  invFun i := i = 1
  left_inv b := by cases b <;> rfl
  right_inv i := by
    rcases i with ⟨i, hi⟩
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> rfl

end Lax53Proofs.FiniteWordStates
