import Lax842588Proofs.StructuralRepresentations

/-!
Pure semantic model for the proof-private iterative traversal of the original
intrinsic formula. It packages subformula occurrences with their indices; it
does not define a second formula syntax or a serialized formula language.
-/

namespace Lax842588Proofs.FormulaArenaTraversalModel

open FirstOrder
open Lax146103.MSOSyntax
open Lax842588.RankedTree
open Lax842588.TreeStructure
open Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators

/-- One occurrence of the original intrinsically scoped formula, together
with the indices determining its type. -/
structure Occurrence (alphabet : RankedAlphabetCode) where
  fo : Nat
  so : Nat
  formula : Formula (treeSignature alphabet.toRankedAlphabet) fo so

namespace Occurrence

def raw {alphabet : RankedAlphabetCode}
    (occurrence : Occurrence alphabet) : Raw :=
  formulaStructure alphabet occurrence.formula

end Occurrence

/-- Symbolic name of the existing intrinsic formula constructor. -/
def constructorName {alphabet : RankedAlphabetCode} {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m) : String :=
  match formula with
  | .falsum => "falsum"
  | .equal _ _ => "equal"
  | .rel _ _ => "rel"
  | .mem _ _ => "mem"
  | .or _ _ => "or"
  | .neg _ => "neg"
  | .exFO _ => "exFO"
  | .exSO _ => "exSO"

/-- Automatic structural derivation makes every formula representation a
named constructor with the constructor's original symbolic name. The fields
remain abstract here because the generic frame loader does not inspect them. -/
theorem formulaStructure_is_constructor {alphabet : RankedAlphabetCode}
    {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    ∃ fields, formulaStructure alphabet formula =
      Raw.constructor (constructorName formula) fields := by
  cases formula <;>
    simp [formulaStructure, constructorName]

/-- Formula occurrences in the exact bottom-up order needed by the compiler.
Only the original formula values are retained. -/
def postorder (alphabet : RankedAlphabetCode) :
    {n m : Nat} →
      Formula (treeSignature alphabet.toRankedAlphabet) n m →
      List (Occurrence alphabet)
  | n, m, formula =>
      match formula with
      | .falsum => [{ fo := n, so := m, formula := formula }]
      | .equal _ _ => [{ fo := n, so := m, formula := formula }]
      | .rel _ _ => [{ fo := n, so := m, formula := formula }]
      | .mem _ _ => [{ fo := n, so := m, formula := formula }]
      | .or left right =>
          postorder alphabet left ++ postorder alphabet right ++
            [{ fo := n, so := m, formula := formula }]
      | .neg body =>
          postorder alphabet body ++
            [{ fo := n, so := m, formula := formula }]
      | .exFO body =>
          postorder alphabet body ++
            [{ fo := n, so := m, formula := formula }]
      | .exSO body =>
          postorder alphabet body ++
            [{ fo := n, so := m, formula := formula }]

@[simp] theorem postorder_falsum (alphabet : RankedAlphabetCode) (n m : Nat) :
    postorder alphabet
      (Formula.falsum :
        Formula (treeSignature alphabet.toRankedAlphabet) n m) =
      [{ fo := n, so := m, formula := .falsum }] := rfl

@[simp] theorem postorder_or (alphabet : RankedAlphabetCode) {n m : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    postorder alphabet (.or left right) =
      postorder alphabet left ++ postorder alphabet right ++
        [{ fo := n, so := m, formula := .or left right }] := rfl

@[simp] theorem postorder_neg (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    postorder alphabet (.neg body) =
      postorder alphabet body ++
        [{ fo := n, so := m, formula := .neg body }] := rfl

@[simp] theorem postorder_exFO (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m) :
    postorder alphabet (.exFO body) =
      postorder alphabet body ++
        [{ fo := n, so := m, formula := .exFO body }] := rfl

@[simp] theorem postorder_exSO (alphabet : RankedAlphabetCode) {n m : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1)) :
    postorder alphabet (.exSO body) =
      postorder alphabet body ++
        [{ fo := n, so := m, formula := .exSO body }] := rfl

/-- Every intrinsic formula contributes at least its own occurrence. -/
theorem postorder_ne_nil (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}
      (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m),
      postorder alphabet formula ≠ [] := by
  intro n m formula
  cases formula <;> simp [postorder]

/-- Number of loop iterations used by the explicit phase-stack traversal.
Atomic occurrences take one iteration, unary constructors take two in
addition to their body, and disjunctions take three in addition to both
subformulas. -/
def traversalSteps (alphabet : RankedAlphabetCode) :
    {n m : Nat} →
      Formula (treeSignature alphabet.toRankedAlphabet) n m → Nat
  | _, _, .falsum => 1
  | _, _, .equal _ _ => 1
  | _, _, .rel _ _ => 1
  | _, _, .mem _ _ => 1
  | _, _, .or left right =>
      traversalSteps alphabet left + traversalSteps alphabet right + 3
  | _, _, .neg body => traversalSteps alphabet body + 2
  | _, _, .exFO body => traversalSteps alphabet body + 2
  | _, _, .exSO body => traversalSteps alphabet body + 2

theorem postorder_length_le_traversalSteps (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}
      (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m),
      (postorder alphabet formula).length ≤ traversalSteps alphabet formula := by
  intro n m formula
  induction formula <;>
    simp_all [postorder, traversalSteps, List.length_append] <;> omega

/-- The traversal overhead is linear in the constructor-derived formula
representation. This is a semantic size statement, independent of the arena
layout used by the implementation. -/
theorem traversalSteps_le_structure (alphabet : RankedAlphabetCode) :
    ∀ {n m : Nat}
      (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m),
      traversalSteps alphabet formula ≤
        3 * (formulaStructure alphabet formula).nodes := by
  intro n m formula
  induction formula <;>
    simp_all [traversalSteps, formulaStructure, Raw.constructor, Raw.fields,
      Raw.nodes] <;> omega

/-- One phase-stack entry. Phase zero means that no child has been visited;
phase one means that a unary body or the left disjunct is complete; phase two
means that both disjuncts are complete. -/
structure TraversalFrame (alphabet : RankedAlphabetCode) where
  occurrence : Occurrence alphabet
  phase : Nat

/-- Output still owed by one valid traversal frame. -/
def framePending (alphabet : RankedAlphabetCode)
    (frame : TraversalFrame alphabet) : List (Occurrence alphabet) :=
  match frame.occurrence with
  | ⟨_, _, formula⟩ =>
      match formula with
      | .falsum | .equal _ _ | .rel _ _ | .mem _ _ => [frame.occurrence]
      | .or left right =>
          if frame.phase = 0 then
            postorder alphabet left ++ postorder alphabet right ++
              [frame.occurrence]
          else if frame.phase = 1 then
            postorder alphabet right ++ [frame.occurrence]
          else [frame.occurrence]
      | .neg body =>
          if frame.phase = 0 then
            postorder alphabet body ++ [frame.occurrence]
          else [frame.occurrence]
      | .exFO body =>
          if frame.phase = 0 then
            postorder alphabet body ++ [frame.occurrence]
          else [frame.occurrence]
      | .exSO body =>
          if frame.phase = 0 then
            postorder alphabet body ++ [frame.occurrence]
          else [frame.occurrence]

/-- Output still owed by the current frame and then every enclosing frame. -/
def pending (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : List (Occurrence alphabet) :=
  frames.flatMap (framePending alphabet)

theorem occurrence_mem_framePending (alphabet : RankedAlphabetCode)
    (frame : TraversalFrame alphabet) :
    frame.occurrence ∈ framePending alphabet frame := by
  rcases frame with ⟨⟨n, m, formula⟩, phase⟩
  cases formula with
  | falsum => simp [framePending]
  | equal => simp [framePending]
  | rel => simp [framePending]
  | mem => simp [framePending]
  | or left right =>
      by_cases hzero : phase = 0
      · simp [framePending, hzero]
      · by_cases hone : phase = 1
        · simp [framePending, hone]
        · simp [framePending, hzero, hone]
  | neg body => by_cases hzero : phase = 0 <;> simp [framePending, hzero]
  | exFO body => by_cases hzero : phase = 0 <;> simp [framePending, hzero]
  | exSO body => by_cases hzero : phase = 0 <;> simp [framePending, hzero]

theorem current_mem_pending (alphabet : RankedAlphabetCode)
    (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) :
    frame.occurrence ∈ pending alphabet (frame :: outer) := by
  simp only [pending, List.flatMap_cons, List.mem_append]
  exact Or.inl (occurrence_mem_framePending alphabet frame)

theorem pending_length_ge_frames (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) :
    frames.length ≤ (pending alphabet frames).length := by
  induction frames with
  | nil => simp [pending]
  | cons frame frames ih =>
      have hnonempty := occurrence_mem_framePending alphabet frame
      have hpos : 0 < (framePending alphabet frame).length := by
        cases hpending : framePending alphabet frame with
        | nil => simp [hpending] at hnonempty
        | cons head tail => simp
      simp only [pending] at ih
      simp only [pending, List.flatMap_cons, List.length_cons,
        List.length_append]
      omega

theorem completed_eq_target (alphabet : RankedAlphabetCode)
    (target produced : List (Occurrence alphabet))
    (hinv : produced ++ pending alphabet [] = target) :
    produced = target := by
  simpa [pending] using hinv

def initialFrame (alphabet : RankedAlphabetCode) {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    TraversalFrame alphabet :=
  ⟨⟨n, m, formula⟩, 0⟩

@[simp] theorem framePending_or (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    framePending alphabet
        ⟨⟨n, m, .or left right⟩, phase⟩ =
      if phase = 0 then
        postorder alphabet left ++ postorder alphabet right ++
          [⟨n, m, .or left right⟩]
      else if phase = 1 then
        postorder alphabet right ++ [⟨n, m, .or left right⟩]
      else [⟨n, m, .or left right⟩] := rfl

@[simp] theorem framePending_neg (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    framePending alphabet ⟨⟨n, m, .neg body⟩, phase⟩ =
      if phase = 0 then postorder alphabet body ++ [⟨n, m, .neg body⟩]
      else [⟨n, m, .neg body⟩] := rfl

@[simp] theorem framePending_exFO (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m) :
    framePending alphabet ⟨⟨n, m, .exFO body⟩, phase⟩ =
      if phase = 0 then postorder alphabet body ++ [⟨n, m, .exFO body⟩]
      else [⟨n, m, .exFO body⟩] := rfl

@[simp] theorem framePending_exSO (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1)) :
    framePending alphabet ⟨⟨n, m, .exSO body⟩, phase⟩ =
      if phase = 0 then postorder alphabet body ++ [⟨n, m, .exSO body⟩]
      else [⟨n, m, .exSO body⟩] := rfl

@[simp] theorem framePending_initial (alphabet : RankedAlphabetCode) {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    framePending alphabet (initialFrame alphabet formula) =
      postorder alphabet formula := by
  cases formula <;> simp [framePending, initialFrame, postorder]

@[simp] theorem pending_initial (alphabet : RankedAlphabetCode) {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    pending alphabet [initialFrame alphabet formula] =
      postorder alphabet formula := by
  cases formula <;> simp [pending, initialFrame, framePending, postorder]

/-- One transition of the explicit phase-stack traversal. -/
def traversalStep (alphabet : RankedAlphabetCode)
    (state : List (Occurrence alphabet) × List (TraversalFrame alphabet)) :
    List (Occurrence alphabet) × List (TraversalFrame alphabet) :=
  match state.2 with
  | [] => state
  | frame :: outer =>
      match frame.occurrence with
      | ⟨_, _, formula⟩ =>
          match formula with
          | .falsum | .equal _ _ | .rel _ _ | .mem _ _ =>
              (state.1 ++ [frame.occurrence], outer)
          | .or left right =>
              if frame.phase = 0 then
                (state.1,
                  initialFrame alphabet left :: ⟨frame.occurrence, 1⟩ :: outer)
              else if frame.phase = 1 then
                (state.1,
                  initialFrame alphabet right :: ⟨frame.occurrence, 2⟩ :: outer)
              else (state.1 ++ [frame.occurrence], outer)
          | .neg body =>
              if frame.phase = 0 then
                (state.1,
                  initialFrame alphabet body :: ⟨frame.occurrence, 1⟩ :: outer)
              else (state.1 ++ [frame.occurrence], outer)
          | .exFO body =>
              if frame.phase = 0 then
                (state.1,
                  initialFrame alphabet body :: ⟨frame.occurrence, 1⟩ :: outer)
              else (state.1 ++ [frame.occurrence], outer)
          | .exSO body =>
              if frame.phase = 0 then
                (state.1,
                  initialFrame alphabet body :: ⟨frame.occurrence, 1⟩ :: outer)
              else (state.1 ++ [frame.occurrence], outer)

theorem traversalStep_preserves_pending (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (frames : List (TraversalFrame alphabet)) :
    (traversalStep alphabet (produced, frames)).1 ++
        pending alphabet (traversalStep alphabet (produced, frames)).2 =
      produced ++ pending alphabet frames := by
  cases frames with
  | nil => simp [traversalStep, pending]
  | cons frame outer =>
      rcases frame with ⟨⟨n, m, formula⟩, phase⟩
      cases formula with
      | falsum => simp [traversalStep, pending, framePending,
          List.append_assoc]
      | equal => simp [traversalStep, pending, framePending,
          List.append_assoc]
      | rel => simp [traversalStep, pending, framePending,
          List.append_assoc]
      | mem => simp [traversalStep, pending, framePending,
          List.append_assoc]
      | or left right =>
          by_cases hzero : phase = 0
          · subst phase
            simp [traversalStep, pending, List.append_assoc]
          · by_cases hone : phase = 1
            · subst phase
              simp [traversalStep, pending, List.append_assoc]
            · simp [traversalStep, pending, hzero, hone,
                List.append_assoc]
      | neg body =>
          by_cases hzero : phase = 0
          · subst phase
            simp [traversalStep, pending, List.append_assoc]
          · simp [traversalStep, pending, hzero,
              List.append_assoc]
      | exFO body =>
          by_cases hzero : phase = 0
          · subst phase
            simp [traversalStep, pending, List.append_assoc]
          · simp [traversalStep, pending, hzero,
              List.append_assoc]
      | exSO body =>
          by_cases hzero : phase = 0
          · subst phase
            simp [traversalStep, pending, List.append_assoc]
          · simp [traversalStep, pending, hzero,
              List.append_assoc]

/-- Exact number of remaining loop iterations represented by a valid frame. -/
def frameWork (alphabet : RankedAlphabetCode)
    (frame : TraversalFrame alphabet) : Nat :=
  match frame.occurrence with
  | ⟨_, _, formula⟩ =>
      match formula with
      | .falsum | .equal _ _ | .rel _ _ | .mem _ _ => 1
      | .or left right =>
          if frame.phase = 0 then
            traversalSteps alphabet left + traversalSteps alphabet right + 3
          else if frame.phase = 1 then traversalSteps alphabet right + 2
          else 1
      | .neg body =>
          if frame.phase = 0 then traversalSteps alphabet body + 2 else 1
      | .exFO body =>
          if frame.phase = 0 then traversalSteps alphabet body + 2 else 1
      | .exSO body =>
          if frame.phase = 0 then traversalSteps alphabet body + 2 else 1

def traversalWork (alphabet : RankedAlphabetCode)
    (frames : List (TraversalFrame alphabet)) : Nat :=
  (frames.map (frameWork alphabet)).sum

@[simp] theorem frameWork_or (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (left right : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    frameWork alphabet ⟨⟨n, m, .or left right⟩, phase⟩ =
      if phase = 0 then
        traversalSteps alphabet left + traversalSteps alphabet right + 3
      else if phase = 1 then traversalSteps alphabet right + 2 else 1 := rfl

@[simp] theorem frameWork_neg (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    frameWork alphabet ⟨⟨n, m, .neg body⟩, phase⟩ =
      if phase = 0 then traversalSteps alphabet body + 2 else 1 := rfl

@[simp] theorem frameWork_exFO (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) (n + 1) m) :
    frameWork alphabet ⟨⟨n, m, .exFO body⟩, phase⟩ =
      if phase = 0 then traversalSteps alphabet body + 2 else 1 := rfl

@[simp] theorem frameWork_exSO (alphabet : RankedAlphabetCode) {n m phase : Nat}
    (body : Formula (treeSignature alphabet.toRankedAlphabet) n (m + 1)) :
    frameWork alphabet ⟨⟨n, m, .exSO body⟩, phase⟩ =
      if phase = 0 then traversalSteps alphabet body + 2 else 1 := rfl

@[simp] theorem initialFrame_work (alphabet : RankedAlphabetCode) {n m : Nat}
    (formula : Formula (treeSignature alphabet.toRankedAlphabet) n m) :
    frameWork alphabet (initialFrame alphabet formula) =
      traversalSteps alphabet formula := by
  cases formula <;> simp [frameWork, initialFrame, traversalSteps]

theorem traversalStep_work (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) :
    traversalWork alphabet
        (traversalStep alphabet (produced, frame :: outer)).2 + 1 =
      traversalWork alphabet (frame :: outer) := by
  rcases frame with ⟨⟨n, m, formula⟩, phase⟩
  cases formula with
  | falsum => simp [traversalStep, traversalWork, frameWork, Nat.add_comm]
  | equal => simp [traversalStep, traversalWork, frameWork, Nat.add_comm]
  | rel => simp [traversalStep, traversalWork, frameWork, Nat.add_comm]
  | mem => simp [traversalStep, traversalWork, frameWork, Nat.add_comm]
  | or left right =>
      by_cases hzero : phase = 0
      · subst phase
        simp [traversalStep, traversalWork, Nat.add_left_comm, Nat.add_comm]
        omega
      · by_cases hone : phase = 1
        · subst phase
          simp [traversalStep, traversalWork, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]
          omega
        · simp [traversalStep, traversalWork, hzero, hone,
            Nat.add_comm]
  | neg body =>
      by_cases hzero : phase = 0
      · subst phase
        simp [traversalStep, traversalWork, Nat.add_assoc,
          Nat.add_comm]
        omega
      · simp [traversalStep, traversalWork, hzero, Nat.add_comm]
  | exFO body =>
      by_cases hzero : phase = 0
      · subst phase
        simp [traversalStep, traversalWork, Nat.add_assoc,
          Nat.add_comm]
        omega
      · simp [traversalStep, traversalWork, hzero, Nat.add_comm]
  | exSO body =>
      by_cases hzero : phase = 0
      · subst phase
        simp [traversalStep, traversalWork, Nat.add_assoc,
          Nat.add_comm]
        omega
      · simp [traversalStep, traversalWork, hzero, Nat.add_comm]

theorem traversalStep_decreases (alphabet : RankedAlphabetCode)
    (produced : List (Occurrence alphabet))
    (frame : TraversalFrame alphabet)
    (outer : List (TraversalFrame alphabet)) :
    traversalWork alphabet
        (traversalStep alphabet (produced, frame :: outer)).2 <
      traversalWork alphabet (frame :: outer) := by
  have h := traversalStep_work alphabet produced frame outer
  omega

end Lax842588Proofs.FormulaArenaTraversalModel
