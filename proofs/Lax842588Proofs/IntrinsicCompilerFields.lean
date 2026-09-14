import Lax842588Proofs.IntrinsicFormulaCompiler
import Lax842588Proofs.FormulaArenaTraversalModel

/-!
Normalized scalar fields consumed by the generic compiler execution bridge.

These six-word rows are proof-private working data derived from occurrences
of the original intrinsically scoped formula. They are not another formula
datatype, an alternate public serialization, or supplied advice. They contain
only the constructor operation, scope counts, and primitive field values;
in particular they contain neither tree data nor global arena addresses.
The charged arena phase must construct them before the generic call.
-/

namespace Lax842588Proofs.IntrinsicCompilerFields

open FirstOrder Lax146103.MSOSyntax
open Lax842588.ValueTranslations Lax842588.TreeStructure
open Lax842588Proofs.FormulaArenaTraversalModel Lax842588Proofs.IntrinsicFormulaCompiler
open Lax842588Proofs.EncodedAutomataOperations Lax842588Proofs.EncodedPrimitiveAtomicAutomata
open Lax842588Proofs.EncodedPrimitiveProjection Lax842588Proofs.EncodedProjection
open Lax842588Proofs.MarkedAlphabetEncoding
open Lax842588Proofs.MarkedTrees

/-- Operation, FO/SO scope counts, and up to three primitive fields.
The operation numbers distinguish the two constructors of the relation field.
All unused slots are zero, so no hidden payload is accepted by this map. -/
def fields {alphabet : RankedAlphabetCode} (o : Occurrence alphabet) : List Nat :=
  match o with
  | ⟨n, m, .falsum⟩ => [0, n, m, 0, 0, 0]
  | ⟨n, m, .equal x y⟩ => [1, n, m, (treeTermVar x).val, (treeTermVar y).val, 0]
  | ⟨n, m, .rel (.label a) ts⟩ => [2, n, m, a.val, (treeTermVar (ts 0)).val, 0]
  | ⟨n, m, .rel (.child i) ts⟩ =>
      [3, n, m, i.val, (treeTermVar (ts 0)).val, (treeTermVar (ts 1)).val]
  | ⟨n, m, .mem x X⟩ => [4, n, m, (treeTermVar x).val, X.val, 0]
  | ⟨n, m, .or _ _⟩ => [5, n, m, 0, 0, 0]
  | ⟨n, m, .neg _⟩ => [6, n, m, 0, 0, 0]
  | ⟨n, m, .exFO _⟩ => [7, n, m, 0, 0, 0]
  | ⟨n, m, .exSO _⟩ => [8, n, m, 0, 0, 0]

theorem fields_length {alphabet : RankedAlphabetCode} (o : Occurrence alphabet) :
    (fields o).length = 6 := by
  obtain ⟨n, m, f⟩ := o
  cases f <;> try rfl
  rename_i relation terms
  cases relation <;> rfl

/-- A total numeric operation on normalized fields and already compiled
children. Unrecognized operation numbers return the rejecting automaton.
Correctness below uses exactly the rows derived from intrinsic formulas. -/
def applyFields (alphabet : RankedAlphabetCode) (row : List Nat)
    (left right : AutomatonCode) : AutomatonCode :=
  let tag := row.getD 0 0
  let n := row.getD 1 0
  let m := row.getD 2 0
  let x := row.getD 3 0
  let y := row.getD 4 0
  let z := row.getD 5 0
  if tag = 0 then emptyCode (code alphabet n m)
  else if tag = 1 then
    inter (code alphabet n m) (validCodeP alphabet n m)
      (somewhereCodeP alphabet n m (fun a => foMarked n m a x && foMarked n m a y))
  else if tag = 2 then
    inter (code alphabet n m) (validCodeP alphabet n m)
      (somewhereCodeP alphabet n m (fun a => decide (baseSymbol n m a = x) && foMarked n m a y))
  else if tag = 3 then
    inter (code alphabet n m) (validCodeP alphabet n m) (edgeCodeP alphabet n m x y z)
  else if tag = 4 then
    inter (code alphabet n m) (validCodeP alphabet n m)
      (somewhereCodeP alphabet n m (fun a => foMarked n m a x && soMarked m a y))
  else if tag = 5 then EncodedComputableDeterminization.union (code alphabet n m) left right
  else if tag = 6 then
    inter (code alphabet n m) (validCodeP alphabet n m)
      (EncodedComputableDeterminization.compl (code alphabet n m) right)
  else if tag = 7 then project (code alphabet n m) (dropFOOfP alphabet n m) right
  else if tag = 8 then project (code alphabet n m) (dropSOOfP alphabet n m) right
  else emptyCode alphabet

def popCount (row : List Nat) : Nat :=
  let tag := row.getD 0 0
  if tag = 5 then 2 else if tag = 6 then 1 else if tag = 7 then 1
    else if tag = 8 then 1 else 0

/-- Stack manipulation is ordinary finite-list computation. Default children
are only used on malformed internal streams, not on genuine postorders. -/
def stackStep (alphabet : RankedAlphabetCode) (stack : List AutomatonCode)
    (row : List Nat) : List AutomatonCode :=
  applyFields alphabet row (stack.getD 1 (1, [], [])) (stack.getD 0 (1, [], [])) ::
    stack.drop (popCount row)

def compileRows (alphabet : RankedAlphabetCode) (rows : List (List Nat)) : AutomatonCode :=
  (rows.foldl (stackStep alphabet) []).getD 0 (1, [], [])

theorem foldl_fields_postorder (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat} (f : Formula (treeSignature alphabet.toRankedAlphabet) n m)
      (stack : List AutomatonCode),
      ((postorder alphabet f).map fields).foldl (stackStep alphabet) stack =
        compileFormula alphabet f :: stack := by
  intro n m f
  induction f with
  | falsum => intro stack; rfl
  | equal x y => intro stack; rfl
  | rel relation ts =>
      intro stack
      cases relation <;> rfl
  | mem x X => intro stack; rfl
  | or f g hf hg =>
      intro stack
      simp only [postorder, List.map_append, List.foldl_append]
      rw [hf, hg]
      rfl
  | neg f hf =>
      intro stack
      simp only [postorder, List.map_append, List.foldl_append]
      rw [hf]
      rfl
  | exFO f hf =>
      intro stack
      simp only [postorder, List.map_append, List.foldl_append]
      rw [hf]
      rfl
  | exSO f hf =>
      intro stack
      simp only [postorder, List.map_append, List.foldl_append]
      rw [hf]
      rfl

theorem compileRows_eq (alphabet : RankedAlphabetCode) {n m : Nat}
    (f : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    compileRows alphabet ((postorder alphabet f).map fields) = compileFormula alphabet f := by
  simp [compileRows, foldl_fields_postorder]

end Lax842588Proofs.IntrinsicCompilerFields
