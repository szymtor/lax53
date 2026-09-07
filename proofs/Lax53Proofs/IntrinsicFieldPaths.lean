import Lax53Proofs.ArenaFieldAccess
import Lax53Proofs.IntrinsicCompilerFields
import Lax58Proofs.StructuralCombinators

/-! Primitive-field paths checked against the generated certified encodings. -/

namespace Lax53Proofs.IntrinsicFieldPaths

open FirstOrder Lax52.MSOSyntax Lax53.ValueTranslations Lax53.TreeStructure
open Lax53.RankedTree
open Lax53.StructuralRepresentations Lax58.StructuralPresentation Lax58.StructuralCombinators
open Lax53Proofs.ArenaFieldAccess Lax53Proofs.MarkedTrees

def firstTerm : List Bool := [true, false, true, false]
def secondTerm : List Bool := [true, true, false, true, false]
def secondField : List Bool := [true, true, false]
def relationTag : List Bool := [true, false, false]
def termZero : List Bool := [true, true, false, false, true, false]
def termOne : List Bool := [true, true, false, true, false, true, false]

theorem tag_eq_iff (a b : String) : Raw.constructorNameCode a = Raw.constructorNameCode b ↔ a = b := by
  constructor
  · intro h
    exact (Lax58Proofs.StructuralCombinators.constructor_eq_iff_proof.mp
      (show Raw.constructor a [] = Raw.constructor b [] by simp only [Raw.constructor, h])).1
  · exact congrArg Raw.constructorNameCode

theorem term_path (a : RankedAlphabetCode) {n : Nat}
    (x : (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (termStructure a x) [true, false] = some (.nat (treeTermVar x).val) := by
  cases x with
  | var x => rfl
  | func f _ => exact nomatch f

theorem equal_first (a : RankedAlphabetCode) {n m : Nat}
    (x y : (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.equal (m := m) x y)) firstTerm =
      some (.nat (treeTermVar x).val) := term_path a x

theorem equal_second (a : RankedAlphabetCode) {n m : Nat}
    (x y : (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.equal (m := m) x y)) secondTerm =
      some (.nat (treeTermVar y).val) := term_path a y

theorem mem_first (a : RankedAlphabetCode) {n m : Nat}
    (x : (treeSignature a.toRankedAlphabet).Term (Fin n)) (X : Fin m) :
    atPath (formulaStructure a (Formula.mem x X)) firstTerm =
      some (.nat (treeTermVar x).val) := term_path a x

theorem mem_second (a : RankedAlphabetCode) {n m : Nat}
    (x : (treeSignature a.toRankedAlphabet).Term (Fin n)) (X : Fin m) :
    atPath (formulaStructure a (Formula.mem x X)) secondField = some (.nat X.val) := rfl

theorem label_value (a : RankedAlphabetCode) {n m : Nat} (symbol : Fin a.length)
    (ts : Fin 1 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.label symbol) ts)) firstTerm =
      some (.nat symbol.val) := rfl

theorem label_tag (a : RankedAlphabetCode) {n m : Nat} (symbol : Fin a.length)
    (ts : Fin 1 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.label symbol) ts)) relationTag =
      some (.nat (Raw.constructorNameCode "label")) := rfl

theorem label_term (a : RankedAlphabetCode) {n m : Nat} (symbol : Fin a.length)
    (ts : Fin 1 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.label symbol) ts)) termZero =
      some (.nat (treeTermVar (ts 0)).val) := term_path a (ts 0)

theorem child_value (a : RankedAlphabetCode) {n m : Nat} (slot : ChildIndex a.toRankedAlphabet)
    (ts : Fin 2 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.child slot) ts)) firstTerm =
      some (.nat slot.val) := rfl

theorem child_tag (a : RankedAlphabetCode) {n m : Nat} (slot : ChildIndex a.toRankedAlphabet)
    (ts : Fin 2 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.child slot) ts)) relationTag =
      some (.nat (Raw.constructorNameCode "child")) := rfl

theorem child_first (a : RankedAlphabetCode) {n m : Nat} (slot : ChildIndex a.toRankedAlphabet)
    (ts : Fin 2 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.child slot) ts)) termZero =
      some (.nat (treeTermVar (ts 0)).val) := term_path a (ts 0)

theorem child_second (a : RankedAlphabetCode) {n m : Nat} (slot : ChildIndex a.toRankedAlphabet)
    (ts : Fin 2 → (treeSignature a.toRankedAlphabet).Term (Fin n)) :
    atPath (formulaStructure a (Formula.rel (m := m) (.child slot) ts)) termOne =
      some (.nat (treeTermVar (ts 1)).val) := term_path a (ts 1)

end Lax53Proofs.IntrinsicFieldPaths
