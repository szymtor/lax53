import Mathlib.Logic.Equiv.Fin.Basic
import Lax53Proofs.EncodedProjection
import Lax53Proofs.FiniteWordStates
import Lax53Proofs.MarkedTrees

namespace Lax53Proofs.MarkedAlphabetEncoding

open Lax53.EffectiveTranslations
open Lax53.RankedTree
open Lax53Proofs.MarkedTrees
open Lax53Proofs.EncodedProjection
open Lax53Proofs.FiniteAutomatonEncoding
open Lax53Proofs.FiniteWordStates

abbrev MarkedSymbol (alphabet : RankedAlphabetCode) (n m : Nat) :=
  (MarkedAlphabet alphabet.toRankedAlphabet n m).Symbol

def symbolCount (alphabet : RankedAlphabetCode) (n m : Nat) : Nat :=
  alphabet.length * (words 2 n).length * (words 2 m).length

abbrev SymbolDigits (alphabet : RankedAlphabetCode) (n m : Nat) :=
  (alphabet.toRankedAlphabet.Symbol × WordState 2 n) × WordState 2 m

/-- Pack a base symbol and its two Boolean marker words into one finite
number. -/
def pack (alphabet : RankedAlphabetCode) (n m : Nat) :
    SymbolDigits alphabet n m ≃ Fin (symbolCount alphabet n m) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

def symbolDigitsEquiv (alphabet : RankedAlphabetCode) (n m : Nat) :
    MarkedSymbol alphabet n m ≃ SymbolDigits alphabet n m where
  toFun s := ((s.1, (wordStateEquiv 2 n).symm (fun i => boolFin (s.2.1 i))),
    (wordStateEquiv 2 m).symm (fun i => boolFin (s.2.2 i)))
  invFun d := (d.1.1,
    fun i => boolFin.symm (wordStateEquiv 2 n d.1.2 i),
    fun i => boolFin.symm (wordStateEquiv 2 m d.2 i))
  left_inv s := by
    rcases s with ⟨a, fo, so⟩
    simp only
    congr 2 <;> funext i <;> simp
  right_inv d := by
    rcases d with ⟨⟨a, fo⟩, so⟩
    simp only
    congr 2
    · exact (wordStateEquiv 2 n).injective (by funext i; simp)
    · exact (wordStateEquiv 2 m).injective (by funext i; simp)

def markedFinEquiv (alphabet : RankedAlphabetCode) (n m : Nat) :
    MarkedSymbol alphabet n m ≃ Fin (symbolCount alphabet n m) :=
  (symbolDigitsEquiv alphabet n m).trans (pack alphabet n m)

/-- The rank word obtained by listing the ranks in explicit enumeration
order. -/
def code (alphabet : RankedAlphabetCode) (n m : Nat) : RankedAlphabetCode :=
  List.ofFn fun i : Fin (symbolCount alphabet n m) =>
    alphabet.toRankedAlphabet.rank ((pack alphabet n m).symm i).1.1

theorem code_length (alphabet : RankedAlphabetCode) (n m : Nat) :
    (code alphabet n m).length = symbolCount alphabet n m := by simp [code]

/-- Number a marked symbol by its index in the explicit enumeration. -/
def toCodeSymbol (alphabet : RankedAlphabetCode) (n m : Nat) :
    MarkedSymbol alphabet n m → (code alphabet n m).toRankedAlphabet.Symbol :=
  fun s => ⟨markedFinEquiv alphabet n m s, by
    simpa [code_length] using (markedFinEquiv alphabet n m s).isLt⟩

/-- Read a marked symbol from its explicit number. -/
def fromCodeSymbol (alphabet : RankedAlphabetCode) (n m : Nat) :
    (code alphabet n m).toRankedAlphabet.Symbol → MarkedSymbol alphabet n m :=
  fun i => (markedFinEquiv alphabet n m).symm
    ⟨i.val, by simpa [code_length] using i.isLt⟩

theorem from_to (alphabet : RankedAlphabetCode) (n m : Nat)
    (s : MarkedSymbol alphabet n m) :
    fromCodeSymbol alphabet n m (toCodeSymbol alphabet n m s) = s := by
  simp [fromCodeSymbol, toCodeSymbol]

theorem to_from (alphabet : RankedAlphabetCode) (n m : Nat)
    (i : (code alphabet n m).toRankedAlphabet.Symbol) :
    toCodeSymbol alphabet n m (fromCodeSymbol alphabet n m i) = i := by
  apply Fin.ext
  simp [toCodeSymbol, fromCodeSymbol]

theorem rank_toCodeSymbol (alphabet : RankedAlphabetCode) (n m : Nat)
    (s : MarkedSymbol alphabet n m) :
    (code alphabet n m).toRankedAlphabet.rank (toCodeSymbol alphabet n m s) =
      (MarkedAlphabet alphabet.toRankedAlphabet n m).rank s := by
  simp only [RankedAlphabetCode.toRankedAlphabet, code, toCodeSymbol,
    List.get_eq_getElem, List.getElem_ofFn]
  change alphabet.toRankedAlphabet.rank
      ((pack alphabet n m).symm (markedFinEquiv alphabet n m s)).1.1 = _
  change alphabet.toRankedAlphabet.rank
      ((pack alphabet n m).symm (markedFinEquiv alphabet n m s)).1.1 =
    alphabet.toRankedAlphabet.rank s.1
  simp [markedFinEquiv, symbolDigitsEquiv]

theorem rank_fromCodeSymbol (alphabet : RankedAlphabetCode) (n m : Nat)
    (i : (code alphabet n m).toRankedAlphabet.Symbol) :
    (MarkedAlphabet alphabet.toRankedAlphabet n m).rank
      (fromCodeSymbol alphabet n m i) =
      (code alphabet n m).toRankedAlphabet.rank i := by
  rw [← rank_toCodeSymbol alphabet n m (fromCodeSymbol alphabet n m i)]
  rw [to_from]

def markedEquiv (alphabet : RankedAlphabetCode) (n m : Nat) :
    MarkedSymbol alphabet n m ≃ (code alphabet n m).toRankedAlphabet.Symbol where
  toFun := toCodeSymbol alphabet n m
  invFun := fromCodeSymbol alphabet n m
  left_inv := from_to alphabet n m
  right_inv := to_from alphabet n m

theorem rank_markedEquiv (alphabet : RankedAlphabetCode) (n m : Nat)
    (s : MarkedSymbol alphabet n m) :
    (code alphabet n m).toRankedAlphabet.rank (markedEquiv alphabet n m s) =
      (MarkedAlphabet alphabet.toRankedAlphabet n m).rank s :=
  rank_toCodeSymbol alphabet n m s

def dropFOMap (alphabet : RankedAlphabetCode) (n m : Nat) :
    (code alphabet (n + 1) m).toRankedAlphabet.Symbol →
      (code alphabet n m).toRankedAlphabet.Symbol :=
  fun a => toCodeSymbol alphabet n m
    (MarkedAlphabet.dropFO (fromCodeSymbol alphabet (n + 1) m a))

def dropSOMap (alphabet : RankedAlphabetCode) (n m : Nat) :
    (code alphabet n (m + 1)).toRankedAlphabet.Symbol →
      (code alphabet n m).toRankedAlphabet.Symbol :=
  fun a => toCodeSymbol alphabet n m
    (MarkedAlphabet.dropSO (fromCodeSymbol alphabet n (m + 1) a))

theorem rank_dropFOMap (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : (code alphabet (n + 1) m).toRankedAlphabet.Symbol) :
    (code alphabet n m).toRankedAlphabet.rank (dropFOMap alphabet n m a) =
      (code alphabet (n + 1) m).toRankedAlphabet.rank a := by
  unfold dropFOMap
  rw [rank_toCodeSymbol]
  exact rank_fromCodeSymbol alphabet (n + 1) m a

theorem rank_dropSOMap (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : (code alphabet n (m + 1)).toRankedAlphabet.Symbol) :
    (code alphabet n m).toRankedAlphabet.rank (dropSOMap alphabet n m a) =
      (code alphabet n (m + 1)).toRankedAlphabet.rank a := by
  unfold dropSOMap
  rw [rank_toCodeSymbol]
  exact rank_fromCodeSymbol alphabet n (m + 1) a

def dropFOOf (alphabet : RankedAlphabetCode) (n m b : Nat) : List Nat :=
  (List.range (code alphabet (n + 1) m).length).filter fun a =>
    match if h : a < (code alphabet (n + 1) m).length then some ⟨a, h⟩ else none with
    | some source => (dropFOMap alphabet n m source).val = b
    | none => false

def dropSOOf (alphabet : RankedAlphabetCode) (n m b : Nat) : List Nat :=
  (List.range (code alphabet n (m + 1)).length).filter fun a =>
    match if h : a < (code alphabet n (m + 1)).length then some ⟨a, h⟩ else none with
    | some source => (dropSOMap alphabet n m source).val = b
    | none => false

theorem mem_dropFOOf (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : (code alphabet (n + 1) m).toRankedAlphabet.Symbol) :
    a.val ∈ dropFOOf alphabet n m (dropFOMap alphabet n m a).val := by
  simp [dropFOOf, a.isLt]

theorem mem_dropSOOf (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : (code alphabet n (m + 1)).toRankedAlphabet.Symbol) :
    a.val ∈ dropSOOf alphabet n m (dropSOMap alphabet n m a).val := by
  simp [dropSOOf, a.isLt]

theorem complete_dropFOOf (alphabet : RankedAlphabetCode) (n m : Nat) :
    CompleteFibers (code alphabet (n + 1) m) (code alphabet n m)
      (dropFOMap alphabet n m) (dropFOOf alphabet n m) := by
  intro b sourceNumber hsource
  simp only [dropFOOf, List.mem_filter, List.mem_range] at hsource
  rcases hsource with ⟨hbound, hmap⟩
  refine ⟨⟨sourceNumber, hbound⟩, rfl, ?_⟩
  simp [hbound] at hmap
  exact Fin.ext hmap

theorem complete_dropSOOf (alphabet : RankedAlphabetCode) (n m : Nat) :
    CompleteFibers (code alphabet n (m + 1)) (code alphabet n m)
      (dropSOMap alphabet n m) (dropSOOf alphabet n m) := by
  intro b sourceNumber hsource
  simp only [dropSOOf, List.mem_filter, List.mem_range] at hsource
  rcases hsource with ⟨hbound, hmap⟩
  refine ⟨⟨sourceNumber, hbound⟩, rfl, ?_⟩
  simp [hbound] at hmap
  exact Fin.ext hmap

def decodeTree (alphabet : RankedAlphabetCode) (n m : Nat) :
    Tree (code alphabet n m).toRankedAlphabet →
      Tree (MarkedAlphabet alphabet.toRankedAlphabet n m) :=
  relabelTree (fromCodeSymbol alphabet n m) (rank_fromCodeSymbol alphabet n m)

theorem decode_codeTree (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    decodeTree alphabet n m
      (relabelTree (toCodeSymbol alphabet n m)
        (rank_toCodeSymbol alphabet n m) t) = t := by
  exact relabelTree_equiv_inverse (markedEquiv alphabet n m)
    (rank_toCodeSymbol alphabet n m) (rank_fromCodeSymbol alphabet n m) t

theorem code_decodeTree (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (code alphabet n m).toRankedAlphabet) :
    relabelTree (toCodeSymbol alphabet n m) (rank_toCodeSymbol alphabet n m)
      (decodeTree alphabet n m t) = t := by
  exact relabelTree_equiv_inverse (markedEquiv alphabet n m).symm
    (rank_fromCodeSymbol alphabet n m) (rank_toCodeSymbol alphabet n m) t

theorem dropFOTree_eq_relabelTree (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet (n + 1) m)) :
    dropFOTree t = relabelTree MarkedAlphabet.dropFO (fun _ => rfl) t := by
  induction t with
  | node a children ih =>
      simp only [dropFOTree, relabelTree]
      congr 1
      funext i
      exact ih i

theorem dropSOTree_eq_relabelTree (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n (m + 1))) :
    dropSOTree t = relabelTree MarkedAlphabet.dropSO (fun _ => rfl) t := by
  induction t with
  | node a children ih =>
      simp only [dropSOTree, relabelTree]
      congr 1
      funext i
      exact ih i

theorem decodeTree_dropFO (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (code alphabet (n + 1) m).toRankedAlphabet) :
    decodeTree alphabet n m
      (mapTree (code alphabet (n + 1) m) (code alphabet n m)
        (dropFOMap alphabet n m) (rank_dropFOMap alphabet n m) t) =
      dropFOTree (decodeTree alphabet (n + 1) m t) := by
  rw [mapTree_eq_relabelTree, decodeTree, relabelTree_comp]
  rw [dropFOTree_eq_relabelTree, decodeTree, relabelTree_comp]
  apply relabelTree_congr
  funext a
  exact from_to alphabet n m _

theorem decodeTree_dropSO (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (code alphabet n (m + 1)).toRankedAlphabet) :
    decodeTree alphabet n m
      (mapTree (code alphabet n (m + 1)) (code alphabet n m)
        (dropSOMap alphabet n m) (rank_dropSOMap alphabet n m) t) =
      dropSOTree (decodeTree alphabet n (m + 1) t) := by
  rw [mapTree_eq_relabelTree, decodeTree, relabelTree_comp]
  rw [dropSOTree_eq_relabelTree, decodeTree, relabelTree_comp]
  apply relabelTree_congr
  funext a
  exact from_to alphabet n m _

end Lax53Proofs.MarkedAlphabetEncoding
