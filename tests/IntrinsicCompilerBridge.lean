import Lax842588Proofs.IntrinsicCompilerOutput
import Lax842588Proofs.CompilerArrayPacking
import Lax842588Proofs.IntrinsicCompilerMaterialize
import Lax842588Proofs.ArenaFieldAccess
import Lax842588Proofs.IntrinsicFieldExtraction
import Lax842588Proofs.IntrinsicOccurrenceInput
import Lax842588Proofs.IntrinsicFormulaInput
import Lax842588Proofs.IntrinsicAlphabetInput
import Lax842588Proofs.IntrinsicCompilerFromArena

/- The internal compiler and its charged numeric-input adapter. No test here
changes the certified public input or asserts end-to-end model checking. -/

set_option autoImplicit false

open Lax842588Proofs.IntrinsicCompilerFields
open Lax842588Proofs.FormulaArenaTraversalModel
open Lax842588Proofs.IntrinsicFormulaCompiler
open Lax146103.MSOSyntax Lax842588.TreeStructure Lax842588.ValueTranslations

#guard popCount [5, 0, 0, 0, 0, 0] = 2
#guard popCount [6, 0, 0, 0, 0, 0] = 1
#guard popCount [7, 0, 0, 0, 0, 0] = 1
#guard popCount [8, 0, 0, 0, 0, 0] = 1
#guard popCount [0, 0, 0, 0, 0, 0] = 0
#guard applyFields [] [99] (7, [], []) (8, [], []) = (1, [], [])
#guard fields (⟨0, 0, .falsum⟩ : Occurrence []) = [0, 0, 0, 0, 0, 0]
#guard fields (⟨0, 0, .exFO (.exSO .falsum)⟩ : Occurrence []) = [7, 0, 0, 0, 0, 0]
#guard compileTable [] [[0, 0, 0, 0, 0, 0]] = [0, 1, 0, 0, 0]

-- The induction covers all constructors and preserves any preexisting stack.
example (alphabet : RankedAlphabetCode) (n m : Nat)
    (f : Formula (treeSignature alphabet.toRankedAlphabet) n m)
    (stack : List AutomatonCode) :
    ((postorder alphabet f).map fields).foldl (stackStep alphabet) stack =
      compileFormula alphabet f :: stack := foldl_fields_postorder alphabet f stack

example : Primrec fun p : RankedAlphabetCode × List (List Nat) => compileRows p.1 p.2 :=
  compileRows_prim

-- Empty and nonempty array prefixes, with no requirement on unused padding.
example : Lax865980Proofs.Reasoning.Spec 16
    (fun σ => Lax842588Proofs.CompilerArrayPacking.Prefix "Data" [] σ ∧ σ.vars "N" = 0)
    (Lax842588Proofs.CompilerArrayPacking.program "Data" "N")
    (fun _ σ => σ.vars "packCode" = 0) 60 :=
  Lax842588Proofs.CompilerArrayPacking.program_spec 16 "Data" "N" [] (by decide)

example : Lax865980Proofs.Reasoning.Spec 512
    (fun σ => Lax842588Proofs.CompilerArrayPacking.Prefix "Data" [2, 0] σ ∧ σ.vars "N" = 2)
    (Lax842588Proofs.CompilerArrayPacking.program "Data" "N")
    (fun _ σ => σ.vars "packCode" = Encodable.encode ([2, 0] : List Nat)) 180 :=
  Lax842588Proofs.CompilerArrayPacking.program_spec 512 "Data" "N" [2, 0] (by decide)

/-- info: 'Lax842588Proofs.IntrinsicCompilerFields.compileRows_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileRows_eq

/-- info: 'Lax842588Proofs.IntrinsicCompilerFields.compileRows_prim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileRows_prim

/-- info: 'Lax842588Proofs.IntrinsicCompilerFields.intrinsicCompiler_ram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms intrinsicCompiler_ram

/-- info: 'Lax842588Proofs.IntrinsicCompilerFields.compileTable_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compileTable_ram

/-- info: 'Lax842588Proofs.CompilerArrayPacking.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.CompilerArrayPacking.program_spec

-- A typed identity code exercises stripping the `some` tag and materializing
-- empty/nonempty outputs. These are internal working data, not public inputs.
example : Lax865980Proofs.Reasoning.Spec 512
    (fun σ => σ.vars (Lax842588Proofs.PrimitiveRecursiveCompile.reg 0) = 0 ∧
      (σ.arrs "P").length = 0)
    (Lax842588Proofs.IntrinsicCompilerMaterialize.materialize .succ "P")
    (fun _ σ => σ.arrs "P" = [] ∧ σ.vars "unpackIndex" = 0)
    (Lax842588Proofs.IntrinsicCompilerMaterialize.timeBound .succ 0) :=
  Lax842588Proofs.IntrinsicCompilerMaterialize.materialize_exact_spec .succ 512 0 "P" []
    rfl (by decide)

example : Lax865980Proofs.Reasoning.Spec 4096
    (fun σ => σ.vars (Lax842588Proofs.PrimitiveRecursiveCompile.reg 0) =
        Encodable.encode ([2, 0] : List Nat) ∧ (σ.arrs "P").length = 2)
    (Lax842588Proofs.IntrinsicCompilerMaterialize.materialize .succ "P")
    (fun _ σ => σ.arrs "P" = [2, 0] ∧ σ.vars "unpackIndex" = 2)
    (Lax842588Proofs.IntrinsicCompilerMaterialize.timeBound .succ
      (Encodable.encode ([2, 0] : List Nat))) :=
  Lax842588Proofs.IntrinsicCompilerMaterialize.materialize_exact_spec .succ 4096
    (Encodable.encode ([2, 0] : List Nat)) "P" [2, 0] rfl (by decide)

#guard Lax842588Proofs.ArenaFieldAccess.atPath
  (.pair (.nat 7) (.pair (.nat 9) (.nat 0))) [true, false] = some (.nat 9)
#guard Lax842588Proofs.ArenaFieldAccess.atPath (.nat 7) [false] = none

/-- info: 'Lax842588Proofs.CompilerArrayUnpacking.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.CompilerArrayUnpacking.program_spec

/-- info: 'Lax842588Proofs.IntrinsicCompilerMaterialize.exists_tableCompiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicCompilerMaterialize.exists_tableCompiler

/-- info: 'Lax842588Proofs.ArenaFieldAccess.load_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.ArenaFieldAccess.load_spec

-- Register packing works without an auxiliary array and counts every pairing.
example : Lax865980Proofs.Reasoning.Spec 512
    (fun σ => [σ.vars "x", σ.vars "y"] = [2, 0])
    (Lax842588Proofs.CompilerArrayPacking.registerProgram "packed" ["x", "y"])
    (fun _ σ => σ.vars "packed" = Encodable.encode ([2, 0] : List Nat)) 75 :=
  Lax842588Proofs.CompilerArrayPacking.registerProgram_spec 512 "packed" ["x", "y"]
    [2, 0] (by decide) (by decide)

example : Lax865980Proofs.Reasoning.Spec 16
    (fun σ => ([] : List String).map σ.vars = [])
    (Lax842588Proofs.CompilerArrayPacking.registerProgram "packed" [])
    (fun _ σ => σ.vars "packed" = Encodable.encode ([] : List Nat)) 25 :=
  Lax842588Proofs.CompilerArrayPacking.registerProgram_spec 16 "packed" [] []
    (by simp) (by decide)

#guard Lax842588Proofs.ArenaFieldAccess.atPath
  (Lax842588.StructuralRepresentations.formulaStructure []
    (Formula.equal (m := 0) (FirstOrder.Language.Term.var (0 : Fin 2))
      (FirstOrder.Language.Term.var (1 : Fin 2))))
  Lax842588Proofs.IntrinsicFieldPaths.secondTerm = some (.nat 1)

#guard Lax842588Proofs.ArenaFieldAccess.atPath
  (Lax842588.StructuralRepresentations.formulaStructure []
    (Formula.mem (FirstOrder.Language.Term.var (0 : Fin 1)) (1 : Fin 2)))
  Lax842588Proofs.IntrinsicFieldPaths.secondField = some (.nat 1)

/-- info: 'Lax842588Proofs.CompilerArrayPacking.registerProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.CompilerArrayPacking.registerProgram_spec

/-- info: 'Lax842588Proofs.IntrinsicFieldExtraction.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicFieldExtraction.program_spec

/-- info: 'Lax842588Proofs.IntrinsicFieldExtraction.packedProgram_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicFieldExtraction.packedProgram_spec

/-- info: 'Lax842588Proofs.IntrinsicOccurrenceInput.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicOccurrenceInput.program_spec

-- Packing a list of row codes is exactly the compiler's list-of-rows encoding.
example (alphabet : RankedAlphabetCode) (os : List (Occurrence alphabet)) :
    Encodable.encode (Lax842588Proofs.IntrinsicFormulaInput.rowCodes os) =
      Encodable.encode (os.map fields) :=
  Lax842588Proofs.IntrinsicFormulaInput.encode_rowCodes os

/-- info: 'Lax842588Proofs.IntrinsicFormulaInput.program_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicFormulaInput.program_spec

example : Lax865980Proofs.Reasoning.Spec 64
    (fun σ => Lax842588Proofs.CompilerArrayPacking.Prefix "P" [0] σ ∧ σ.vars "A" = 0)
    Lax842588Proofs.IntrinsicAlphabetInput.program
    (fun _ σ => σ.vars "packCode" = 0) 450 :=
  Lax842588Proofs.IntrinsicAlphabetInput.program_spec 64 [] (by decide)

/-- info: 'Lax842588Proofs.IntrinsicAlphabetInput.from_alphabetRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicAlphabetInput.from_alphabetRead

/-- info: 'Lax842588Proofs.IntrinsicCompilerFromArena.exists_compiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax842588Proofs.IntrinsicCompilerFromArena.exists_compiler
