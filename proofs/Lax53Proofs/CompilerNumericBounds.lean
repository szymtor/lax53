import Lax53Proofs.PrimitiveRecursiveBounds
import Lax53Proofs.CompilerArrayPacking
import Mathlib.Computability.Primrec.List

/-! Primitive-recursive bounds for bounded lists and finite ranges of compiler inputs. -/

namespace Lax53Proofs.CompilerNumericBounds

open Encodable Lax53Proofs.PrimitiveRecursiveBounds

def listBound (M n : Nat) : Nat := (fun v => pairCap M v + 1)^[n] 0

@[simp] theorem listBound_zero (M : Nat) : listBound M 0 = 0 := rfl

@[simp] theorem listBound_succ (M n : Nat) :
    listBound M (n + 1) = pairCap M (listBound M n) + 1 := by
  simp [listBound, Function.iterate_succ_apply']

theorem listBound_prim : Primrec₂ listBound :=
  Primrec.nat_iterate Primrec.snd (Primrec.const 0)
    (Primrec.nat_add.comp
      (pairCap_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (Primrec.const 1))

theorem listBound_mono (M : Nat) : Monotone (listBound M) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [listBound_succ]
  have h := (Nat.right_le_pair M (listBound M n)).trans
    (pair_le_cap le_rfl le_rfl)
  omega

theorem encode_list_bound (M : Nat) (xs : List Nat)
    (hvalues : ∀ v ∈ xs, v ≤ M) : encode xs ≤ listBound M xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hvalues x (by simp)
    have ht := ih (fun v hv => hvalues v (by simp [hv]))
    simp only [encode_list_cons, List.length_cons, listBound_succ]
    exact Nat.add_le_add_right (pair_le_cap hx ht) 1

theorem encode_list_le (M n : Nat) (xs : List Nat)
    (hlen : xs.length ≤ n) (hvalues : ∀ v ∈ xs, v ≤ M) : encode xs ≤ listBound M n :=
  (encode_list_bound M xs hvalues).trans (listBound_mono M hlen)

def prefixMax (f : Nat → Nat) (N : Nat) : Nat :=
  ((List.range (N + 1)).map f).foldl max 0

theorem fold_max_ge (xs : List Nat) (seed : Nat) : seed ≤ xs.foldl max seed := by
  induction xs generalizing seed with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left seed x).trans (ih (max seed x))

theorem fold_max_mem (xs : List Nat) (seed v : Nat) (hv : v ∈ xs) : v ≤ xs.foldl max seed := by
  induction xs generalizing seed with
  | nil => simp at hv
  | cons x xs ih =>
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact (le_max_right seed v).trans (fold_max_ge xs (max seed v))
    · exact ih (max seed x) hv

theorem le_prefixMax (f : Nat → Nat) {n N : Nat} (h : n ≤ N) : f n ≤ prefixMax f N := by
  apply fold_max_mem
  exact List.mem_map.mpr ⟨n, List.mem_range.mpr (by omega), rfl⟩

theorem prefixMax_prim {f : Nat → Nat} (hf : Primrec f) : Primrec (prefixMax f) := by
  have hxs : Primrec (fun N => (List.range (N + 1)).map f) :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 1)))
      (hf.comp Primrec.snd)
  exact Primrec.list_foldl (h := fun (_ : Nat) p => max p.1 p.2)
    hxs (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

end Lax53Proofs.CompilerNumericBounds
