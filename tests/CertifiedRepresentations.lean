import Lax842588.StructuralRepresentations

/- Run from concepts/: lake env lean ../tests/CertifiedRepresentations.lean -/

open Lax842588.StructuralRepresentations
open Lax842588.ValueTranslations Lax842588.RankedTree
open Lax842588.TreeStructure (treeSignature)
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators
open Lax146103.MSOSyntax

set_option autoImplicit false

example (alphabet : RankedAlphabetCode) {n : Nat} (i : Fin n) :
    termStructure alphabet (.var i) = Raw.constructor "var" [Raw.nat i.val] := rfl

example (alphabet : RankedAlphabetCode) (i : ChildIndex alphabet.toRankedAlphabet) :
    relationStructure alphabet (.child i) = Raw.constructor "child" [Raw.nat i.val] := rfl

example (alphabet : RankedAlphabetCode) {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m) :
    formulaStructure alphabet (.exFO formula) =
      Raw.constructor "exFO" [formulaStructure alphabet formula] := rfl

example (alphabet : RankedAlphabetCode) (a : alphabet.toRankedAlphabet.Symbol)
    (children : Fin (alphabet.toRankedAlphabet.rank a) → Tree alphabet.toRankedAlphabet) :
    treeStructure alphabet (.node a children) = Raw.constructor "node"
      (Raw.nat a.val :: List.ofFn fun i => treeStructure alphabet (children i)) := by
  simp only [treeStructure, List.append_nil,
    Lax560851.CertifiedDerivation.CertifiedFieldEncoding.fin]

/-- info: 'Lax842588.StructuralRepresentations.termStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termStructure.certified

/-- info: 'Lax842588.StructuralRepresentations.relationStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relationStructure.certified

/-- info: 'Lax842588.StructuralRepresentations.formulaStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms formulaStructure.certified

/-- info: 'Lax842588.StructuralRepresentations.treeStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStructure.certified
