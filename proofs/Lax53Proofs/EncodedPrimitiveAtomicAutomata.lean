import Lax53Proofs.EncodedComputableDeterminization
import Lax53Proofs.EncodedAtomicAutomata
import Mathlib.Data.List.GetD

namespace Lax53Proofs.EncodedPrimitiveAtomicAutomata

open Lax53.ValueTranslations
open Lax53Proofs.FiniteAutomatonEncoding
open Lax53Proofs.FiniteWordStates
open Lax53Proofs.MarkedAlphabetEncoding
open Lax53Proofs.EncodedAtomicAutomata
open Lax53Proofs.EncodedAutomataComputability
open Lax53Proofs.EncodedComputableDeterminization
open Lax53.RankedTree
open Lax53Proofs.MarkedTrees
open Lax53Proofs.ValidMarkedTrees
open Lax53Proofs.AtomicMarkedTrees
open Lax53Proofs.EncodedProjection

/-- The digit at a position of a canonically enumerated finite word. -/
def wordDigit (base length state position : Nat) : Nat :=
  ((words base length).getD state []).getD position 0

def binaryWordCount (length : Nat) : Nat := (words 2 length).length

/-- Arithmetic projections from the packed marked-symbol number. -/
def baseSymbol (n m symbol : Nat) : Nat :=
  symbol / binaryWordCount m / binaryWordCount n

def foWord (n m symbol : Nat) : Nat :=
  symbol / binaryWordCount m % binaryWordCount n

def foMarked (n m symbol x : Nat) : Bool :=
  decide (wordDigit 2 n (foWord n m symbol) x = 1)

def soMarked (m symbol X : Nat) : Bool :=
  decide (wordDigit 2 m (symbol % binaryWordCount m) X = 1)

/-- The explicit rank string of the packed marked alphabet. -/
def numericCode (alphabet : RankedAlphabetCode) (n m : Nat) : RankedAlphabetCode :=
  (List.range (symbolCount alphabet n m)).map fun symbol =>
    alphabet.getD (baseSymbol n m symbol) 0

theorem wordDigit_prim : Primrec fun
    p : Nat × Nat × Nat × Nat =>
      wordDigit p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold wordDigit
  have hword : Primrec fun p : Nat × Nat × Nat × Nat =>
      (words p.1 p.2.1).getD p.2.2.1 [] :=
    (Primrec.list_getD ([] : List Nat)).comp
      (words_prim.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_getD 0 |>.comp hword
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem binaryWordCount_prim : Primrec binaryWordCount := by
  unfold binaryWordCount
  exact Primrec.list_length.comp <|
    words_prim.comp (Primrec.const 2) Primrec.id

theorem symbolCount_prim : Primrec fun p : RankedAlphabetCode × Nat × Nat =>
    symbolCount p.1 p.2.1 p.2.2 := by
  unfold symbolCount
  exact Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.list_length.comp Primrec.fst)
      (binaryWordCount_prim.comp <| Primrec.fst.comp Primrec.snd))
    (binaryWordCount_prim.comp <| Primrec.snd.comp Primrec.snd)

theorem baseSymbol_prim : Primrec fun p : Nat × Nat × Nat =>
    baseSymbol p.1 p.2.1 p.2.2 := by
  unfold baseSymbol
  exact Primrec.nat_div.comp
    (Primrec.nat_div.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))
      (binaryWordCount_prim.comp <| Primrec.fst.comp Primrec.snd))
    (binaryWordCount_prim.comp Primrec.fst)

theorem foWord_prim : Primrec fun p : Nat × Nat × Nat =>
    foWord p.1 p.2.1 p.2.2 := by
  unfold foWord
  exact Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.snd.comp Primrec.snd)
      (binaryWordCount_prim.comp <| Primrec.fst.comp Primrec.snd))
    (binaryWordCount_prim.comp Primrec.fst)

theorem foMarked_prim : Primrec fun p : Nat × Nat × Nat × Nat =>
    foMarked p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold foMarked
  have hdigit : Primrec fun p : Nat × Nat × Nat × Nat =>
      wordDigit 2 p.1 (foWord p.1 p.2.1 p.2.2.1) p.2.2.2 := by
    exact wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
      Primrec.pair Primrec.fst <| Primrec.pair
        (foWord_prim.comp <| Primrec.pair Primrec.fst <|
          Primrec.pair (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.eq.comp hdigit (Primrec.const 1)).decide

theorem soMarked_prim : Primrec fun p : Nat × Nat × Nat =>
    soMarked p.1 p.2.1 p.2.2 := by
  unfold soMarked
  exact (Primrec.eq.comp
    (wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
      Primrec.pair Primrec.fst <| Primrec.pair
        (Primrec.nat_mod.comp
          (Primrec.fst.comp Primrec.snd)
          (binaryWordCount_prim.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))
    (Primrec.const 1)).decide

theorem numericCode_prim : Primrec fun p : RankedAlphabetCode × Nat × Nat =>
    numericCode p.1 p.2.1 p.2.2 := by
  unfold numericCode
  apply Primrec.list_map (Primrec.list_range.comp symbolCount_prim)
  exact Primrec.list_getD 0 |>.comp
    (Primrec.fst.comp Primrec.fst)
    (baseSymbol_prim.comp <| Primrec.pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) <|
        Primrec.pair
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)

theorem code_eq_numeric (alphabet : RankedAlphabetCode) (n m : Nat) :
    code alphabet n m = numericCode alphabet n m := by
  apply List.ext_get
  · simp [code, numericCode]
  · intro i hcode hnumeric
    have h₁ : i < symbolCount alphabet n m := by
      simpa [code] using hcode
    have h₂ : i < symbolCount alphabet n m := by
      simpa [numericCode] using hnumeric
    simp only [code, numericCode, List.length_ofFn, List.length_map,
      List.length_range]
    rw [List.get_ofFn]
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    simp only [RankedAlphabetCode.toRankedAlphabet, List.get_eq_getElem]
    unfold baseSymbol binaryWordCount pack
    have hbn : 0 < (words 2 n).length := by
      exact List.length_pos_iff.mpr <|
        List.ne_nil_of_mem (bits_mem_words n (fun _ => false))
    have hbm : 0 < (words 2 m).length := by
      exact List.length_pos_iff.mpr <|
        List.ne_nil_of_mem (bits_mem_words m (fun _ => false))
    let j : Fin alphabet.length :=
      (((finProdFinEquiv.prodCongr (Equiv.refl (WordState 2 m))).trans
        finProdFinEquiv).symm
          (Fin.cast (code_length alphabet n m) ⟨i, hcode⟩)).1.1
    change alphabet[j.val] =
      alphabet.getD (i / (words 2 m).length / (words 2 n).length) 0
    have hbase : j.val =
        i / (words 2 m).length / (words 2 n).length := by
      unfold j
      change i / (words 2 m).length / (words 2 n).length = _
      rfl
    calc
      alphabet[j.val] = alphabet.getD j.val 0 := by
        simp [List.getD_eq_getElem?_getD, j.isLt]
      _ = alphabet.getD
          (i / (words 2 m).length / (words 2 n).length) 0 :=
        congrArg (fun q => alphabet.getD q 0) hbase

theorem code_prim : Primrec fun p : RankedAlphabetCode × Nat × Nat =>
    code p.1 p.2.1 p.2.2 := by
  exact numericCode_prim.of_eq fun p => (code_eq_numeric p.1 p.2.1 p.2.2).symm

def allZero (digits : List Nat) : Bool := digits.all fun d => d = 0

def exactlyOne (digits : List Nat) : Bool :=
  (List.range digits.length).any fun i =>
    digits.getD i 2 = 1 &&
      (List.range digits.length).all fun j => j = i || digits.getD j 2 = 0

def occurrenceStep (atRoot : Bool) (digits : List Nat) : Nat :=
  if !atRoot && allZero digits then 0
  else if atRoot && allZero digits || !atRoot && exactlyOne digits then 1
  else 2

def validTransitionP (n m a q : Nat) (children : List Nat) : Bool :=
  (List.range n).all fun x =>
    wordDigit 3 n q x = occurrenceStep (foMarked n m a x)
      (children.map fun child => wordDigit 3 n child x)

def validAcceptP (n q : Nat) : Bool :=
  (List.range n).all fun x => wordDigit 3 n q x = 1

def validCodeP (alphabet : RankedAlphabetCode) (n m : Nat) : AutomatonCode :=
  FiniteAutomatonEncoding.encode (code alphabet n m) (words 3 n).length
    (fun a q children => validTransitionP n m a q children)
    (fun q => validAcceptP n q)

def somewhereCodeP (alphabet : RankedAlphabetCode) (n m : Nat)
    (pred : Nat → Bool) : AutomatonCode :=
  FiniteAutomatonEncoding.encode (code alphabet n m) 2
    (fun a q children =>
      decide (q = (pred a || children.any fun child => child = 1).toNat))
    (fun q => q = 1)

def edgeTransitionP (n m slot x y a q : Nat) (children : List Nat) : Bool :=
  let parentMarkers := (List.range n).all fun z =>
    wordDigit 2 (n + 1) q z = (foMarked n m a z).toNat
  let hasDone := children.any fun child => wordDigit 2 (n + 1) child n = 1
  let hasEdge := wordDigit 2 (n + 1) (children.getD slot 0) y = 1
  parentMarkers && decide (wordDigit 2 (n + 1) q n =
    (hasDone || foMarked n m a x && hasEdge).toNat)

def edgeCodeP (alphabet : RankedAlphabetCode) (n m slot x y : Nat) : AutomatonCode :=
  FiniteAutomatonEncoding.encode (code alphabet n m) (words 2 (n + 1)).length
    (edgeTransitionP n m slot x y)
    (fun q => wordDigit 2 (n + 1) q n = 1)

theorem allZero_prim : Primrec fun digits : List Nat => allZero digits := by
  have hrel : PrimrecPred fun d : Nat => d = 0 :=
    Primrec.eq.comp Primrec.id (Primrec.const 0)
  exact hrel.forall_mem_list.decide.of_eq fun digits => by
    apply Bool.eq_iff_iff.mpr
    simp [allZero]

theorem exactlyOne_prim : Primrec fun digits : List Nat => exactlyOne digits := by
  let P := Nat × List Nat
  have hone : Primrec fun p : P => decide (p.2.getD p.1 2 = 1) :=
    (Primrec.eq.comp
      (Primrec.list_getD 2 |>.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)).decide
  have hinnerRel : PrimrecRel fun (j : Nat) (p : P) =>
      j = p.1 ∨ p.2.getD j 2 = 0 := by
    exact ((Primrec.eq.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)).primrecRel).or
      ((Primrec.eq.comp
        (Primrec.list_getD 2 |>.comp
          (Primrec.snd.comp Primrec.snd) Primrec.fst)
        (Primrec.const 0)).primrecRel)
  have hinner : Primrec fun p : P =>
      (List.range p.2.length).all fun j => j = p.1 ∨ p.2.getD j 2 = 0 :=
    hinnerRel.forall_mem_list.decide.comp
        (Primrec.list_range.comp <| Primrec.list_length.comp Primrec.snd)
        Primrec.id
      |>.of_eq fun p => by
        apply Bool.eq_iff_iff.mpr
        simp
  have htest : Primrec fun p : P =>
      decide (p.2.getD p.1 2 = 1) &&
        (List.range p.2.length).all fun j => j = p.1 ∨ p.2.getD j 2 = 0 :=
    Primrec.and.comp hone hinner
  have hrel : PrimrecRel fun (i : Nat) (digits : List Nat) =>
      (digits.getD i 2 = 1 &&
        (List.range digits.length).all fun j => j = i ∨ digits.getD j 2 = 0) = true :=
    (Primrec.eq.comp htest (Primrec.const true)).primrecRel
  exact hrel.exists_mem_list.decide.comp
      (Primrec.list_range.comp Primrec.list_length) Primrec.id
    |>.of_eq fun digits => by
      apply Bool.eq_iff_iff.mpr
      simp [exactlyOne]

theorem occurrenceStep_prim : Primrec fun p : Bool × List Nat =>
    occurrenceStep p.1 p.2 := by
  unfold occurrenceStep
  have hz : Primrec fun p : Bool × List Nat =>
      !p.1 && allZero p.2 :=
    Primrec.and.comp (Primrec.not.comp Primrec.fst)
      (allZero_prim.comp Primrec.snd)
  have ho : Primrec fun p : Bool × List Nat =>
      p.1 && allZero p.2 || !p.1 && exactlyOne p.2 :=
    Primrec.or.comp
      (Primrec.and.comp Primrec.fst (allZero_prim.comp Primrec.snd))
      (Primrec.and.comp (Primrec.not.comp Primrec.fst)
        (exactlyOne_prim.comp Primrec.snd))
  exact (Primrec.cond hz (Primrec.const 0)
    (Primrec.cond ho (Primrec.const 1) (Primrec.const 2))).of_eq fun p => by
      cases hz' : (!p.1 && allZero p.2) <;>
        cases ho' : (p.1 && allZero p.2 || !p.1 && exactlyOne p.2) <;>
        simp [hz', ho']

theorem listAll_prim {X Y : Type*} [Primcodable X] [Primcodable Y]
    (items : X → List Y) (pred : X → Y → Bool)
    (hitems : Primrec items)
    (hpred : Primrec fun p : X × Y => pred p.1 p.2) :
    Primrec fun x => (items x).all (pred x) := by
  have hrel : PrimrecRel fun (y : Y) (x : X) => pred x y = true := by
    exact (Primrec.eq.comp
      (hpred.comp <| Primrec.pair Primrec.snd Primrec.fst)
      (Primrec.const true)).primrecRel
  exact hrel.forall_mem_list.decide.comp hitems Primrec.id
    |>.of_eq fun x => by
      apply Bool.eq_iff_iff.mpr
      simp

theorem listAny_prim {X Y : Type*} [Primcodable X] [Primcodable Y]
    (items : X → List Y) (pred : X → Y → Bool)
    (hitems : Primrec items)
    (hpred : Primrec fun p : X × Y => pred p.1 p.2) :
    Primrec fun x => (items x).any (pred x) := by
  have hrel : PrimrecRel fun (y : Y) (x : X) => pred x y = true := by
    exact (Primrec.eq.comp
      (hpred.comp <| Primrec.pair Primrec.snd Primrec.fst)
      (Primrec.const true)).primrecRel
  exact hrel.exists_mem_list.decide.comp hitems Primrec.id
    |>.of_eq fun x => by
      apply Bool.eq_iff_iff.mpr
      simp

theorem validTransitionP_prim {X : Type*} [Primcodable X]
    (n m a q : X → Nat) (children : X → List Nat)
    (hn : Primrec n) (hm : Primrec m) (ha : Primrec a) (hq : Primrec q)
    (hchildren : Primrec children) :
    Primrec fun x => validTransitionP (n x) (m x) (a x) (q x) (children x) := by
  have hfo : Primrec fun p : X × Nat =>
      foMarked (n p.1) (m p.1) (a p.1) p.2 :=
    foMarked_prim.comp <| Primrec.pair (hn.comp Primrec.fst) <|
      Primrec.pair (hm.comp Primrec.fst) <|
        Primrec.pair (ha.comp Primrec.fst) Primrec.snd
  have hdigits : Primrec fun p : X × Nat =>
      (children p.1).map fun child => wordDigit 3 (n p.1) child p.2 := by
    apply Primrec.list_map (hchildren.comp Primrec.fst)
    exact wordDigit_prim.comp <| Primrec.pair (Primrec.const 3) <|
      Primrec.pair (hn.comp <| Primrec.fst.comp Primrec.fst) <|
        Primrec.pair Primrec.snd
          (Primrec.snd.comp Primrec.fst)
  have hocc : Primrec fun p : X × Nat => occurrenceStep
      (foMarked (n p.1) (m p.1) (a p.1) p.2)
      ((children p.1).map fun child => wordDigit 3 (n p.1) child p.2) :=
    occurrenceStep_prim.comp <| Primrec.pair hfo hdigits
  have hparent : Primrec fun p : X × Nat =>
      wordDigit 3 (n p.1) (q p.1) p.2 :=
    wordDigit_prim.comp <| Primrec.pair (Primrec.const 3) <|
      Primrec.pair (hn.comp Primrec.fst) <|
        Primrec.pair (hq.comp Primrec.fst) Primrec.snd
  unfold validTransitionP
  exact listAll_prim
    (fun x => List.range (n x))
    (fun x z => wordDigit 3 (n x) (q x) z = occurrenceStep
      (foMarked (n x) (m x) (a x) z)
      ((children x).map fun child => wordDigit 3 (n x) child z))
    (Primrec.list_range.comp hn)
    (Primrec.eq.comp hparent hocc).decide

theorem validAcceptP_prim {X : Type*} [Primcodable X]
    (n q : X → Nat) (hn : Primrec n) (hq : Primrec q) :
    Primrec fun x => validAcceptP (n x) (q x) := by
  unfold validAcceptP
  apply listAll_prim (fun x => List.range (n x))
    (fun x z => wordDigit 3 (n x) (q x) z = 1)
    (Primrec.list_range.comp hn)
  exact (Primrec.eq.comp
    (wordDigit_prim.comp <| Primrec.pair (Primrec.const 3) <|
      Primrec.pair (hn.comp Primrec.fst) <|
        Primrec.pair (hq.comp Primrec.fst) Primrec.snd)
    (Primrec.const 1)).decide

theorem validCodeP_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (n m : X → Nat)
    (halphabet : Primrec alphabet) (hn : Primrec n) (hm : Primrec m) :
    Primrec fun x => validCodeP (alphabet x) (n x) (m x) := by
  unfold validCodeP
  apply encode_prim
    (fun x => code (alphabet x) (n x) (m x))
    (fun x => (words 3 (n x)).length)
    (fun x a q children => validTransitionP (n x) (m x) a q children)
    (fun x q => validAcceptP (n x) q)
  · exact code_prim.comp <| Primrec.pair halphabet (Primrec.pair hn hm)
  · exact Primrec.list_length.comp <|
      words_prim.comp (Primrec.const 3) hn
  · exact validTransitionP_prim
      (fun p : X × Nat × Nat × List Nat => n p.1)
      (fun p => m p.1) (fun p => p.2.1)
      (fun p => p.2.2.1) (fun p => p.2.2.2)
      (hn.comp Primrec.fst) (hm.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
  · exact validAcceptP_prim
      (fun p : X × Nat => n p.1) (fun p => p.2)
      (hn.comp Primrec.fst) Primrec.snd

theorem somewhereCodeP_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode) (n m : X → Nat)
    (pred : X → Nat → Bool)
    (halphabet : Primrec alphabet) (hn : Primrec n) (hm : Primrec m)
    (hpred : Primrec fun p : X × Nat => pred p.1 p.2) :
    Primrec fun x => somewhereCodeP (alphabet x) (n x) (m x) (pred x) := by
  unfold somewhereCodeP
  apply encode_prim
    (fun x => code (alphabet x) (n x) (m x)) (fun _ => 2)
    (fun x a q children =>
      decide (q = (pred x a || children.any fun child => child = 1).toNat))
    (fun _ q => q = 1)
  · exact code_prim.comp <| Primrec.pair halphabet (Primrec.pair hn hm)
  · exact Primrec.const 2
  · let P := X × Nat × Nat × List Nat
    have hany : Primrec fun p : P => p.2.2.2.any fun child => child = 1 := by
      apply listAny_prim (fun p : P => p.2.2.2) (fun _ child => child = 1)
      · exact Primrec.snd.comp <| Primrec.snd.comp Primrec.snd
      · exact (Primrec.eq.comp Primrec.snd (Primrec.const 1)).decide
    have hor : Primrec fun p : P =>
        pred p.1 p.2.1 || p.2.2.2.any fun child => child = 1 :=
      Primrec.or.comp
        (hpred.comp <| Primrec.pair Primrec.fst
          (Primrec.fst.comp Primrec.snd)) hany
    have hnat : Primrec fun p : P =>
        (pred p.1 p.2.1 || p.2.2.2.any fun child => child = 1).toNat :=
      (Primrec.dom_bool Bool.toNat).comp hor
    exact (Primrec.eq.comp
      (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd) hnat).decide
  · exact (Primrec.eq.comp Primrec.snd (Primrec.const 1)).decide

theorem edgeTransitionP_prim {X : Type*} [Primcodable X]
    (n m slot x y a q : X → Nat) (children : X → List Nat)
    (hn : Primrec n) (hm : Primrec m) (hslot : Primrec slot)
    (hx : Primrec x) (hy : Primrec y) (ha : Primrec a) (hq : Primrec q)
    (hchildren : Primrec children) :
    Primrec fun z => edgeTransitionP (n z) (m z) (slot z) (x z) (y z)
      (a z) (q z) (children z) := by
  have hfoAt : Primrec fun p : X × Nat =>
      foMarked (n p.1) (m p.1) (a p.1) p.2 :=
    foMarked_prim.comp <| Primrec.pair (hn.comp Primrec.fst) <|
      Primrec.pair (hm.comp Primrec.fst) <|
        Primrec.pair (ha.comp Primrec.fst) Primrec.snd
  have hparentDigit : Primrec fun p : X × Nat =>
      wordDigit 2 (n p.1 + 1) (q p.1) p.2 :=
    wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
      Primrec.pair
        (Primrec.succ.comp <| hn.comp Primrec.fst) <|
          Primrec.pair (hq.comp Primrec.fst) Primrec.snd
  have hparentMarkers : Primrec fun z =>
      (List.range (n z)).all fun i =>
        wordDigit 2 (n z + 1) (q z) i = (foMarked (n z) (m z) (a z) i).toNat := by
    apply listAll_prim (fun z => List.range (n z))
      (fun z i => wordDigit 2 (n z + 1) (q z) i =
        (foMarked (n z) (m z) (a z) i).toNat)
      (Primrec.list_range.comp hn)
    exact (Primrec.eq.comp hparentDigit
      ((Primrec.dom_bool Bool.toNat).comp hfoAt)).decide
  have hchildDone : Primrec fun p : X × Nat =>
      decide (wordDigit 2 (n p.1 + 1) p.2 (n p.1) = 1) :=
    (Primrec.eq.comp
      (wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
        Primrec.pair (Primrec.succ.comp <| hn.comp Primrec.fst) <|
          Primrec.pair Primrec.snd (hn.comp Primrec.fst))
      (Primrec.const 1)).decide
  have hhasDone : Primrec fun z => (children z).any fun child =>
      wordDigit 2 (n z + 1) child (n z) = 1 :=
    listAny_prim children
      (fun z child => wordDigit 2 (n z + 1) child (n z) = 1)
      hchildren hchildDone
  have hchildAt : Primrec fun z => (children z).getD (slot z) 0 :=
    Primrec.list_getD 0 |>.comp hchildren hslot
  have hhasEdge : Primrec fun z =>
      decide (wordDigit 2 (n z + 1) ((children z).getD (slot z) 0) (y z) = 1) :=
    (Primrec.eq.comp
      (wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
        Primrec.pair (Primrec.succ.comp hn) <|
          Primrec.pair hchildAt hy)
      (Primrec.const 1)).decide
  have hfoX : Primrec fun z => foMarked (n z) (m z) (a z) (x z) :=
    foMarked_prim.comp <| Primrec.pair hn <|
      Primrec.pair hm (Primrec.pair ha hx)
  have hexpected : Primrec fun z =>
      ((children z).any (fun child =>
          wordDigit 2 (n z + 1) child (n z) = 1) ||
        foMarked (n z) (m z) (a z) (x z) &&
          wordDigit 2 (n z + 1) ((children z).getD (slot z) 0) (y z) = 1).toNat :=
    (Primrec.dom_bool Bool.toNat).comp <|
      Primrec.or.comp hhasDone (Primrec.and.comp hfoX hhasEdge)
  have hparentLast : Primrec fun z => wordDigit 2 (n z + 1) (q z) (n z) :=
    wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
      Primrec.pair (Primrec.succ.comp hn) (Primrec.pair hq hn)
  unfold edgeTransitionP
  exact Primrec.and.comp hparentMarkers
    ((Primrec.eq.comp hparentLast hexpected).decide)

theorem edgeCodeP_prim {X : Type*} [Primcodable X]
    (alphabet : X → RankedAlphabetCode)
    (n m slot x y : X → Nat)
    (halphabet : Primrec alphabet) (hn : Primrec n) (hm : Primrec m)
    (hslot : Primrec slot) (hx : Primrec x) (hy : Primrec y) :
    Primrec fun z => edgeCodeP (alphabet z) (n z) (m z)
      (slot z) (x z) (y z) := by
  unfold edgeCodeP
  apply encode_prim
    (fun z => code (alphabet z) (n z) (m z))
    (fun z => (words 2 (n z + 1)).length)
    (fun z a q children => edgeTransitionP (n z) (m z)
      (slot z) (x z) (y z) a q children)
    (fun z q => wordDigit 2 (n z + 1) q (n z) = 1)
  · exact code_prim.comp <| Primrec.pair halphabet (Primrec.pair hn hm)
  · exact Primrec.list_length.comp <| words_prim.comp (Primrec.const 2)
      (Primrec.succ.comp hn)
  · let P := X × Nat × Nat × List Nat
    exact edgeTransitionP_prim
      (fun p : P => n p.1) (fun p => m p.1) (fun p => slot p.1)
      (fun p => x p.1) (fun p => y p.1) (fun p => p.2.1)
      (fun p => p.2.2.1) (fun p => p.2.2.2)
      (hn.comp Primrec.fst) (hm.comp Primrec.fst)
      (hslot.comp Primrec.fst) (hx.comp Primrec.fst) (hy.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
  · exact (Primrec.eq.comp
      (wordDigit_prim.comp <| Primrec.pair (Primrec.const 2) <|
        Primrec.pair (Primrec.succ.comp <| hn.comp Primrec.fst) <|
          Primrec.pair Primrec.snd (hn.comp Primrec.fst))
      (Primrec.const 1)).decide

theorem wordDigit_wordState (base length : Nat) (state : WordState base length)
    (position : Fin length) :
    wordDigit base length state.val position.val =
      (wordStateEquiv base length state position).val := by
  unfold wordDigit wordStateEquiv toFun decode
  have hstate : (words base length).getD state.val [] =
      (words base length).get state := by
    simp [List.getD_eq_getElem?_getD, state.isLt]
  rw [hstate]
  have hposition : position.val < ((words base length).get state).length := by
    change position.val < (decode base length state).length
    rw [decode_length]
    exact position.isLt
  rw [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem hposition]
  rfl

theorem packed_base (alphabet : RankedAlphabetCode) (n m : Nat)
    (symbol : (code alphabet n m).toRankedAlphabet.Symbol) :
    ((pack alphabet n m).symm
      (Fin.cast (code_length alphabet n m) symbol)).1.1.val =
      baseSymbol n m symbol.val := by
  unfold baseSymbol binaryWordCount pack
  change symbol.val / (words 2 m).length / (words 2 n).length = _
  rfl

theorem packed_fo (alphabet : RankedAlphabetCode) (n m : Nat)
    (symbol : (code alphabet n m).toRankedAlphabet.Symbol) :
    ((pack alphabet n m).symm
      (Fin.cast (code_length alphabet n m) symbol)).1.2.val =
      foWord n m symbol.val := by
  unfold foWord binaryWordCount pack
  change symbol.val / (words 2 m).length % (words 2 n).length = _
  rfl

theorem packed_so (alphabet : RankedAlphabetCode) (n m : Nat)
    (symbol : (code alphabet n m).toRankedAlphabet.Symbol) :
    ((pack alphabet n m).symm
      (Fin.cast (code_length alphabet n m) symbol)).2.val =
      symbol.val % binaryWordCount m := by
  unfold binaryWordCount pack
  change symbol.val % (words 2 m).length = _
  rfl

theorem fromCode_base (alphabet : RankedAlphabetCode) (n m : Nat)
    (symbol : (code alphabet n m).toRankedAlphabet.Symbol) :
    (fromCodeSymbol alphabet n m symbol).1.val = baseSymbol n m symbol.val := by
  unfold fromCodeSymbol markedFinEquiv symbolDigitsEquiv
  exact packed_base alphabet n m symbol

theorem fromCode_fo (alphabet : RankedAlphabetCode) (n m : Nat)
    (symbol : (code alphabet n m).toRankedAlphabet.Symbol) (x : Fin n) :
    (fromCodeSymbol alphabet n m symbol).2.1 x =
      foMarked n m symbol.val x.val := by
  let state : WordState 2 n := ((pack alphabet n m).symm
    (Fin.cast (code_length alphabet n m) symbol)).1.2
  change boolFin.symm (wordStateEquiv 2 n state x) =
    decide (wordDigit 2 n (foWord n m symbol.val) x.val = 1)
  have hstate : state.val = foWord n m symbol.val := packed_fo alphabet n m symbol
  rw [← hstate, wordDigit_wordState]
  rcases h : wordStateEquiv 2 n state x with ⟨d, hd⟩
  have : d = 0 ∨ d = 1 := by omega
  rcases this with rfl | rfl <;> rfl

theorem fromCode_so (alphabet : RankedAlphabetCode) (n m : Nat)
    (symbol : (code alphabet n m).toRankedAlphabet.Symbol) (X : Fin m) :
    (fromCodeSymbol alphabet n m symbol).2.2 X =
      soMarked m symbol.val X.val := by
  let state : WordState 2 m := ((pack alphabet n m).symm
    (Fin.cast (code_length alphabet n m) symbol)).2
  change boolFin.symm (wordStateEquiv 2 m state X) =
    decide (wordDigit 2 m (symbol.val % binaryWordCount m) X.val = 1)
  have hstate : state.val = symbol.val % binaryWordCount m :=
    packed_so alphabet n m symbol
  rw [← hstate, wordDigit_wordState]
  rcases h : wordStateEquiv 2 m state X with ⟨d, hd⟩
  have : d = 0 ∨ d = 1 := by omega
  rcases this with rfl | rfl <;> rfl

theorem foMarked_toCode (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : MarkedSymbol alphabet n m) (x : Fin n) :
    foMarked n m (toCodeSymbol alphabet n m a).val x.val = a.2.1 x := by
  rw [← fromCode_fo alphabet n m (toCodeSymbol alphabet n m a) x]
  rw [from_to]

theorem allZero_eq_true_iff (digits : List Nat) :
    allZero digits = true ↔ ∀ d ∈ digits, d = 0 := by
  simp [allZero]

theorem exactlyOne_eq_true_iff (digits : List Nat) :
    exactlyOne digits = true ↔
      ∃ i : Fin digits.length, digits.get i = 1 ∧
        ∀ j : Fin digits.length, j ≠ i → digits.get j = 0 := by
  simp only [exactlyOne, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hone, hrest⟩
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · simpa [List.getD_eq_getElem?_getD, hi] using hone
    · intro j hji
      have hj := hrest j.val j.isLt
      rcases hj with hval | hzero
      · exact False.elim (hji (Fin.ext hval))
      · simpa [List.getD_eq_getElem?_getD, j.isLt] using hzero
  · rintro ⟨i, hone, hrest⟩
    refine ⟨i.val, i.isLt, ?_, ?_⟩
    · simpa [List.getD_eq_getElem?_getD, i.isLt] using hone
    · intro j hj
      by_cases hji : j = i.val
      · exact Or.inl hji
      · right
        have hfin : (⟨j, hj⟩ : Fin digits.length) ≠ i := by
          intro h
          exact hji (congrArg Fin.val h)
        simpa [List.getD_eq_getElem?_getD, hj] using hrest ⟨j, hj⟩ hfin

theorem occurrenceStep_valid {k : Nat} (parent : OccurrenceCount)
    (atRoot : Bool) (children : Fin k → OccurrenceCount) :
    ValidStep parent atRoot children ↔
      (occurrenceFin parent).val = occurrenceStep atRoot
        (List.ofFn fun i => (occurrenceFin (children i)).val) := by
  classical
  have hzero : allZero (List.ofFn fun i =>
      (occurrenceFin (children i)).val) = true ↔ ∀ i, children i = .zero := by
    rw [allZero_eq_true_iff]
    constructor
    · intro h i
      apply occurrenceFin.injective
      apply Fin.ext
      exact h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · intro h d hd
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
      simp [h i, occurrenceFin]
  have hone : exactlyOne (List.ofFn fun i =>
      (occurrenceFin (children i)).val) = true ↔
      ∃ i, children i = .one ∧ ∀ j, j ≠ i → children j = .zero := by
    rw [exactlyOne_eq_true_iff]
    let hlen : (List.ofFn fun i => (occurrenceFin (children i)).val).length = k :=
      List.length_ofFn
    constructor
    · rintro ⟨i, hi, hrest⟩
      let i' : Fin k := Fin.cast hlen i
      refine ⟨i', ?_, ?_⟩
      · apply occurrenceFin.injective
        apply Fin.ext
        simpa [i', hlen] using hi
      intro j hji
      let j' : Fin (List.ofFn fun i => (occurrenceFin (children i)).val).length :=
        Fin.cast hlen.symm j
      have hjne : j' ≠ i := by
        intro hji'
        apply hji
        apply Fin.ext
        simpa [j', i'] using congrArg Fin.val hji'
      have heq0 : occurrenceFin (children j) = (0 : Fin 3) := by
        simpa [j', hlen] using hrest j' hjne
      have heq : occurrenceFin (children j) = occurrenceFin .zero := by
        simpa [occurrenceFin] using heq0
      exact occurrenceFin.injective heq
    · rintro ⟨i, hi, hrest⟩
      let i' : Fin (List.ofFn fun i => (occurrenceFin (children i)).val).length :=
        Fin.cast hlen.symm i
      refine ⟨i', ?_, ?_⟩
      · simpa [i', hlen, hi, occurrenceFin]
      · intro j hji
        let j' : Fin k := Fin.cast hlen j
        have hjne : j' ≠ i := by
          intro hji'
          apply hji
          apply Fin.ext
          simpa [j', i'] using congrArg Fin.val hji'
        rw [List.get_ofFn]
        rw [show Fin.cast hlen j = j' by rfl, hrest j' hjne]
        rfl
  cases hz : allZero (List.ofFn fun i => (occurrenceFin (children i)).val) <;>
    cases ho : exactlyOne (List.ofFn fun i => (occurrenceFin (children i)).val) <;>
    cases parent <;> cases atRoot <;>
    simp [ValidStep, zeroStep, oneStep, occurrenceStep, occurrenceFin,
      hz, ho, hzero, hone] at *
  all_goals aesop

theorem validDigit (n : Nat) (q : ValidState n) (x : Fin n) :
    wordDigit 3 n q.val x.val = (occurrenceFin (validStateEquiv n q x)).val := by
  rw [wordDigit_wordState]
  simp [validStateEquiv]

theorem validStep_cast {k l : Nat} (h : k = l) (parent : OccurrenceCount)
    (atRoot : Bool) (children : Fin l → OccurrenceCount) :
    ValidStep parent atRoot (fun i : Fin k => children (Fin.cast h i)) ↔
      ValidStep parent atRoot children := by
  cases h
  rfl

theorem validP_transition (alphabet : RankedAlphabetCode) (n m : Nat)
    (a : MarkedSymbol alphabet n m) (parent : Fin n → OccurrenceCount)
    (children : Fin ((MarkedAlphabet alphabet.toRankedAlphabet n m).rank a) →
      (Fin n → OccurrenceCount)) :
    ((validCodeP alphabet n m).toAutomaton (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) ((validStateEquiv n).symm parent)
        (fun i => (validStateEquiv n).symm
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) =
      (validMarkedAutomaton alphabet.toRankedAlphabet n m).transition
        a parent children := by
  classical
  unfold validCodeP
  rw [FiniteAutomatonEncoding.transition_encode]
  unfold validTransitionP validMarkedAutomaton
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h x
    have hx := h x.val (List.mem_range.mpr x.isLt)
    have hchildren :
        (List.ofFn ((fun child => wordDigit 3 n child x.val) ∘
          fun i => ((validStateEquiv n).symm
            (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))).val)) =
        (List.ofFn fun i => (occurrenceFin
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i) x)).val) := by
      apply List.ext_get
      · simp
      · intro i hi₁ hi₂
        simp only [List.get_ofFn, Function.comp_apply]
        rw [validDigit, Equiv.apply_symm_apply]
        apply congrArg (fun j => (occurrenceFin (children j x)).val)
        apply Fin.ext
        rfl
    have hx' : (occurrenceFin (parent x)).val = occurrenceStep (a.2.1 x)
        (List.ofFn fun i => (occurrenceFin
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i) x)).val) := by
      rw [validDigit, Equiv.apply_symm_apply,
        foMarked_toCode alphabet n m a x] at hx
      simp only [List.map_ofFn] at hx
      rw [hchildren] at hx
      exact hx
    have hv := (occurrenceStep_valid (parent x) (a.2.1 x)
      (fun i => children (Fin.cast (rank_toCodeSymbol alphabet n m a) i) x)).mpr hx'
    exact (validStep_cast (rank_toCodeSymbol alphabet n m a) (parent x)
      (a.2.1 x) (fun i => children i x)).mp hv
  · intro h z hz
    let x : Fin n := ⟨z, List.mem_range.mp hz⟩
    have hv : ValidStep (parent x) (a.2.1 x)
        (fun i => children (Fin.cast (rank_toCodeSymbol alphabet n m a) i) x) := by
      exact (validStep_cast (rank_toCodeSymbol alphabet n m a) (parent x)
        (a.2.1 x) (fun i => children i x)).mpr (h x)
    have hx' := (occurrenceStep_valid (parent x) (a.2.1 x)
      (fun i => children (Fin.cast (rank_toCodeSymbol alphabet n m a) i) x)).mp hv
    have hchildren :
        (List.ofFn ((fun child => wordDigit 3 n child x.val) ∘
          fun i => ((validStateEquiv n).symm
            (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))).val)) =
        (List.ofFn fun i => (occurrenceFin
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i) x)).val) := by
      apply List.ext_get
      · simp
      · intro i hi₁ hi₂
        simp only [List.get_ofFn, Function.comp_apply]
        rw [validDigit, Equiv.apply_symm_apply]
        apply congrArg (fun j => (occurrenceFin (children j x)).val)
        apply Fin.ext
        rfl
    change wordDigit 3 n ((validStateEquiv n).symm parent).val x.val = _
    rw [validDigit, Equiv.apply_symm_apply,
      foMarked_toCode alphabet n m a x]
    simp only [List.map_ofFn]
    rw [hchildren]
    exact hx'

theorem validP_accept (alphabet : RankedAlphabetCode) (n m : Nat)
    (q : Fin n → OccurrenceCount) :
    ((validCodeP alphabet n m).toAutomaton (code alphabet n m)).accept
        ((validStateEquiv n).symm q) =
      (validMarkedAutomaton alphabet.toRankedAlphabet n m).accept q := by
  classical
  calc
    _ = ((validCode alphabet n m).toAutomaton (code alphabet n m)).accept
        ((validStateEquiv n).symm q) := by
      unfold validCodeP validCode
      rw [FiniteAutomatonEncoding.accept_encode,
        FiniteAutomatonEncoding.accept_encode]
      simp only [fin?_fin]
      unfold validAcceptP
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, decide_eq_true_eq]
      constructor
      · intro h x
        have hx := h x.val (by simpa using x.isLt)
        rw [validDigit] at hx
        apply occurrenceFin.injective
        apply Fin.ext
        simpa [occurrenceFin] using hx
      · intro h z hz
        let x : Fin n := ⟨z, by simpa using hz⟩
        change wordDigit 3 n ((validStateEquiv n).symm q).val x.val = 1
        rw [validDigit, h x]
        rfl
    _ = _ := valid_accept alphabet n m q

theorem validCodeP_accepts_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    ((validCodeP alphabet n m).toAutomaton (code alphabet n m)).Accepts
        (codeTree alphabet n m t) ↔
      t ∈ validMarkedLanguage alphabet.toRankedAlphabet n m := by
  rw [← validMarkedAutomaton_correct alphabet.toRankedAlphabet n m]
  exact relabelTree_accepts_iff (toCodeSymbol alphabet n m)
    (rank_toCodeSymbol alphabet n m) (validStateEquiv n).symm
    (validMarkedAutomaton alphabet.toRankedAlphabet n m)
    ((validCodeP alphabet n m).toAutomaton (code alphabet n m))
    (validP_transition alphabet n m) (validP_accept alphabet n m) t

theorem somewhereP_transition (alphabet : RankedAlphabetCode) (n m : Nat)
    (predNum : Nat → Bool) (pred : MarkedSymbol alphabet n m → Bool)
    (hpred : ∀ a : (code alphabet n m).toRankedAlphabet.Symbol,
      predNum a.val = pred (fromCodeSymbol alphabet n m a))
    (a : MarkedSymbol alphabet n m) (parent : Bool)
    (children : Fin ((MarkedAlphabet alphabet.toRankedAlphabet n m).rank a) → Bool) :
    ((somewhereCodeP alphabet n m predNum).toAutomaton
      (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) (boolFin parent)
        (fun i => boolFin (children
          (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) =
      (somewhereAutomaton pred).transition a parent children := by
  calc
    _ = ((somewhereCode alphabet n m pred).toAutomaton
        (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) (boolFin parent)
        (fun i => boolFin (children
          (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) := by
      unfold somewhereCodeP somewhereCode
      rw [FiniteAutomatonEncoding.transition_encode,
        FiniteAutomatonEncoding.transition_encode]
      simp only [fin?_fin]
      rw [hpred, from_to]
    _ = _ := somewhere_transition alphabet n m pred a parent children

theorem somewhereP_accept (alphabet : RankedAlphabetCode) (n m : Nat)
    (predNum : Nat → Bool) (pred : MarkedSymbol alphabet n m → Bool)
    (q : Bool) :
    ((somewhereCodeP alphabet n m predNum).toAutomaton
      (code alphabet n m)).accept (boolFin q) =
      (somewhereAutomaton pred).accept q := by
  calc
    _ = ((somewhereCode alphabet n m pred).toAutomaton
        (code alphabet n m)).accept (boolFin q) := by
      unfold somewhereCodeP somewhereCode
      rw [FiniteAutomatonEncoding.accept_encode,
        FiniteAutomatonEncoding.accept_encode]
    _ = _ := somewhere_accept alphabet n m pred q

theorem somewhereCodeP_accepts_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (predNum : Nat → Bool) (pred : MarkedSymbol alphabet n m → Bool)
    (hpred : ∀ a : (code alphabet n m).toRankedAlphabet.Symbol,
      predNum a.val = pred (fromCodeSymbol alphabet n m a))
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    ((somewhereCodeP alphabet n m predNum).toAutomaton
      (code alphabet n m)).Accepts (codeTree alphabet n m t) ↔ Somewhere pred t := by
  rw [← somewhere_accepts_iff pred t]
  exact relabelTree_accepts_iff (toCodeSymbol alphabet n m)
    (rank_toCodeSymbol alphabet n m) boolFin (somewhereAutomaton pred)
    ((somewhereCodeP alphabet n m predNum).toAutomaton (code alphabet n m))
    (somewhereP_transition alphabet n m predNum pred hpred)
    (somewhereP_accept alphabet n m predNum pred) t

theorem boolToNat_injective : Function.Injective Bool.toNat := by
  intro a b h
  cases a <;> cases b <;> simp at h ⊢

theorem finTwo_boolToNat (d : Fin 2) : d.val = (boolFin.symm d).toNat := by
  rcases d with ⟨d, hd⟩
  have : d = 0 ∨ d = 1 := by omega
  rcases this with rfl | rfl <;> rfl

theorem edgeMarkerDigit (n : Nat) (q : EdgeCodeState n) (z : Fin n) :
    wordDigit 2 (n + 1) q.val z.val = ((edgeStateEquiv n q).1 z).toNat := by
  have h := wordDigit_wordState 2 (n + 1) q z.castSucc
  rw [show z.castSucc.val = z.val by rfl] at h
  change wordDigit 2 (n + 1) q.val z.val =
    (boolFin.symm (wordStateEquiv 2 (n + 1) q z.castSucc)).toNat
  exact h.trans (finTwo_boolToNat _)

theorem edgeDoneDigit (n : Nat) (q : EdgeCodeState n) :
    wordDigit 2 (n + 1) q.val n = (edgeStateEquiv n q).2.toNat := by
  have h := wordDigit_wordState 2 (n + 1) q (Fin.last n)
  rw [show (Fin.last n).val = n by rfl] at h
  change wordDigit 2 (n + 1) q.val n =
    (boolFin.symm (wordStateEquiv 2 (n + 1) q (Fin.last n))).toNat
  exact h.trans (finTwo_boolToNat _)

theorem wordsTwo_head (length : Nat) :
    (words 2 length).head? = some (List.replicate length 0) := by
  induction length with
  | zero => rfl
  | succ length ih =>
      simp [words, show List.range 2 = [0, 1] by decide, ih,
        List.replicate_succ]

theorem wordsTwo_getD_zero (length : Nat) :
    (words 2 length).getD 0 [] = List.replicate length 0 := by
  have hpos : 0 < (words 2 length).length := by
    exact List.length_pos_iff.mpr <|
      List.ne_nil_of_mem (bits_mem_words length (fun _ => false))
  rw [List.getD_eq_getElem (l := words 2 length) (d := []) hpos]
  have h := wordsTwo_head length
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at h
  exact Option.some.inj h

theorem zeroWordDigit (length position : Nat) :
    wordDigit 2 length 0 position = 0 := by
  unfold wordDigit
  rw [wordsTwo_getD_zero]
  by_cases h : position < length
  · rw [List.getD_eq_getElem (l := List.replicate length 0) (d := 0)
      (by simpa using h)]
    simp
  · rw [List.getD_eq_default (l := List.replicate length 0) (d := 0)
      (by simpa using h)]

theorem edgeP_transition (alphabet : RankedAlphabetCode) (n m : Nat)
    (slot : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n)
    (a : MarkedSymbol alphabet n m) (parent : EdgeState n)
    (children : Fin ((MarkedAlphabet alphabet.toRankedAlphabet n m).rank a) →
      EdgeState n) :
    ((edgeCodeP alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m)).transition
        (toCodeSymbol alphabet n m a) ((edgeStateEquiv n).symm parent)
        (fun i => (edgeStateEquiv n).symm
          (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))) =
      (edgeAutomaton (m := m) slot x y).transition a parent children := by
  unfold edgeCodeP
  rw [FiniteAutomatonEncoding.transition_encode]
  unfold edgeTransitionP edgeAutomaton
  let codedChildren := List.ofFn fun i => ((edgeStateEquiv n).symm
    (children (Fin.cast (rank_toCodeSymbol alphabet n m a) i))).val
  have hmarkers : (List.range n).all (fun z =>
      wordDigit 2 (n + 1) ((edgeStateEquiv n).symm parent).val z =
        (foMarked n m (toCodeSymbol alphabet n m a).val z).toNat) =
      decide (parent.1 = a.2.1) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      funext z
      have hz := h z.val (List.mem_range.mpr z.isLt)
      have hz' := of_decide_eq_true hz
      rw [edgeMarkerDigit, Equiv.apply_symm_apply,
        foMarked_toCode alphabet n m a z] at hz'
      exact boolToNat_injective hz'
    · intro h z hz
      let i : Fin n := ⟨z, by simpa using hz⟩
      apply decide_eq_true
      rw [show z = i.val by rfl, edgeMarkerDigit, Equiv.apply_symm_apply,
        foMarked_toCode alphabet n m a i, h]
  have hdone : codedChildren.any (fun child =>
      wordDigit 2 (n + 1) child n = 1) = decide (∃ i, (children i).2 = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, hc, htrue⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      let j := Fin.cast (rank_toCodeSymbol alphabet n m a) i
      refine ⟨j, ?_⟩
      rw [edgeDoneDigit, Equiv.apply_symm_apply] at htrue
      have htrue' := of_decide_eq_true htrue
      simpa [j] using Bool.toNat_eq_one.mp htrue'
    · rintro ⟨j, hj⟩
      let i := Fin.cast (rank_toCodeSymbol alphabet n m a).symm j
      refine ⟨((edgeStateEquiv n).symm (children j)).val, ?_, ?_⟩
      · exact List.mem_ofFn.mpr ⟨i, by simp [codedChildren, i]⟩
      · rw [edgeDoneDigit, Equiv.apply_symm_apply, hj]
        rfl
  have hedge : decide (wordDigit 2 (n + 1)
      (codedChildren.getD slot.val 0) y.val = 1) =
      decide (∃ i, i.val = slot.val ∧ (children i).1 y = true) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    by_cases hs : slot.val < codedChildren.length
    · let ci : Fin ((code alphabet n m).toRankedAlphabet.rank
          (toCodeSymbol alphabet n m a)) := ⟨slot.val, by
            simpa [codedChildren] using hs⟩
      let j := Fin.cast (rank_toCodeSymbol alphabet n m a) ci
      have hget : codedChildren.getD slot.val 0 =
          ((edgeStateEquiv n).symm (children j)).val := by
        rw [List.getD_eq_getElem (l := codedChildren) (d := 0) hs]
        simp [codedChildren, j, ci]
      rw [hget, edgeMarkerDigit, Equiv.apply_symm_apply]
      constructor
      · intro hy
        exact ⟨j, by simp [j, ci], by simpa using Bool.toNat_eq_one.mp hy⟩
      · rintro ⟨i, hi, hiy⟩
        have hij : i = j := by
          apply Fin.ext
          simpa [j, ci] using hi
        subst i
        simp [hiy]
    · have hget : codedChildren.getD slot.val 0 = 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hs)]
      rw [hget, zeroWordDigit]
      simp only [Nat.zero_ne_one, false_iff]
      rintro ⟨i, hi, -⟩
      apply hs
      have hi' : i.val < (code alphabet n m).toRankedAlphabet.rank
          (toCodeSymbol alphabet n m a) := by
        rw [rank_toCodeSymbol]
        exact i.isLt
      have hi'' : slot.val < (code alphabet n m).toRankedAlphabet.rank
          (toCodeSymbol alphabet n m a) := hi ▸ hi'
      simpa [codedChildren] using hi''
  rw [hmarkers]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [edgeDoneDigit, Equiv.apply_symm_apply, hdone, hedge]
  rw [foMarked_toCode]
  constructor
  · rintro ⟨hmark, hlast⟩
    refine ⟨hmark, ?_⟩
    have hb := Bool.eq_iff_iff.mp (boolToNat_injective hlast)
    simpa using hb
  · rintro ⟨hmark, hlast⟩
    refine ⟨hmark, ?_⟩
    apply congrArg Bool.toNat
    apply Bool.eq_iff_iff.mpr
    simpa using hlast

theorem edgeP_accept (alphabet : RankedAlphabetCode) (n m : Nat)
    (slot : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n)
    (q : EdgeState n) :
    ((edgeCodeP alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m)).accept ((edgeStateEquiv n).symm q) =
      (edgeAutomaton (m := m) slot x y).accept q := by
  unfold edgeCodeP
  rw [FiniteAutomatonEncoding.accept_encode]
  unfold edgeAutomaton
  rw [edgeDoneDigit, Equiv.apply_symm_apply]
  change decide (q.2.toNat = 1) = q.2
  cases q.2 <;> decide

theorem edgeCodeP_accepts_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (slot : ChildIndex alphabet.toRankedAlphabet) (x y : Fin n)
    (t : Tree (MarkedAlphabet alphabet.toRankedAlphabet n m)) :
    ((edgeCodeP alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m)).Accepts (codeTree alphabet n m t) ↔
      EdgeSomewhere slot x y t := by
  rw [← edge_accepts_iff (m := m) slot x y t]
  exact relabelTree_accepts_iff (toCodeSymbol alphabet n m)
    (rank_toCodeSymbol alphabet n m) (edgeStateEquiv n).symm
    (edgeAutomaton (m := m) slot x y)
    ((edgeCodeP alphabet n m slot.val x.val y.val).toAutomaton
      (code alphabet n m))
    (edgeP_transition alphabet n m slot x y)
    (edgeP_accept alphabet n m slot x y) t

end Lax53Proofs.EncodedPrimitiveAtomicAutomata
