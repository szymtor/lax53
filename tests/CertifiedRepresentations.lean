import Lax53.StructuralRepresentations

/- Run from concepts/: lake env lean ../tests/CertifiedRepresentations.lean -/

open Lax53.StructuralRepresentations
open Lax53.ValueTranslations Lax53.RankedTree
open Lax53.TreeStructure (treeSignature)
open Lax58.StructuralPresentation Lax58.StructuralCombinators
open Lax52.MSOSyntax

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
    Lax58.CertifiedDerivation.CertifiedFieldEncoding.fin]

/-- info: 'Lax53.StructuralRepresentations.termStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms termStructure.certified

/-- info: 'Lax53.StructuralRepresentations.relationStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relationStructure.certified

/-- info: 'Lax53.StructuralRepresentations.formulaStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms formulaStructure.certified

/-- info: 'Lax53.StructuralRepresentations.treeStructure.certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeStructure.certified
