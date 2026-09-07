import Lax53Proofs.PrimitiveRecursiveAutomata

/- Run from proofs/: lake env lean ../tests/PrimitiveRecursiveBridge.lean.
These tests audit the generic compiler and its first actual RAM application.
The one-word interface remains internal; this is not yet the uniform MSO
compiler accepting certified arenas. -/

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax53Proofs.PrimitiveRecursiveCode Lax53Proofs.PrimitiveRecursivePairing
open Lax53Proofs.PrimitiveRecursiveCompile Lax53Proofs.PrimitiveRecursiveBounds
open Lax53Proofs.PrimitiveRecursiveCorrectness
open Lax53Proofs.PrimitiveRecursiveRam

set_option autoImplicit false

#guard Code.eval .left (Nat.pair 0 0) = 0
#guard Code.eval .right (Nat.pair 3 7) = 7
#guard Code.eval (.pair .succ .left) 5 = Nat.pair 6 (Nat.unpair 5).1
#guard Code.eval (.comp .succ .succ) 3 = 5

-- The primitive-recursion convention passes (parameter, (counter, accumulator)).
-- This source program computes addition; both semantics and execution are checked.
#guard Code.eval (.prec (.pair .left .right) (.comp .succ (.comp .right .right)))
  (Nat.pair 3 4) = 7

example : Correct (.pair (.comp .succ .succ) .right) :=
  correct_pair (correct_comp correct_succ correct_succ) correct_right

example : Correct (.prec (.pair .left .right) (.comp .succ (.comp .right .right))) :=
  compile_correct _

-- An actual RAM theorem, including the zero-iteration boundary case.
example : Lax13.RamComputes.ComputesInTime 16 (program (.prec .zero .succ)) {[0]}
    (fun _ => [0]) (fun _ => timeBound (.prec .zero .succ) 0) :=
  code_computes (.prec .zero .succ) 0 16 (by decide)

example (w : Nat)
    (hw : wordBound (.prec (.pair .left .right) (.comp .succ (.comp .right .right)))
      (Nat.pair 3 4) ≤ 2 ^ w) :
    Lax13.RamComputes.ComputesInTime w
      (program (.prec (.pair .left .right) (.comp .succ (.comp .right .right))))
      {[Nat.pair 3 4]} (fun _ => [7])
      (fun _ => timeBound (.prec (.pair .left .right) (.comp .succ (.comp .right .right)))
        (Nat.pair 3 4)) := by
  have heval : Code.eval (.prec (.pair .left .right) (.comp .succ (.comp .right .right)))
      (Nat.pair 3 4) = 7 := by
    norm_num [Code.eval]
    rfl
  simpa only [heval] using code_computes _ (Nat.pair 3 4) w hw

-- Zero-input and aliased-output cases are covered by the actual bounded proofs.
example : Spec 4 (fun σ => σ.vars "x" = 0) (unpairLeftProgram "x" "s" "x")
    (fun _ σ => σ.vars "x" = 0) 60 :=
  unpairLeft_spec 4 0 "x" "s" "x" (by decide) (by decide)

example (B a b : Nat) (hB : (a + b + 1) ^ 2 < B) :
    Spec B (fun σ => σ.vars "x" = a ∧ σ.vars "y" = b) (pairProgram "x" "y" "x")
      (fun _ σ => σ.vars "x" = Nat.pair a b) 20 := pair_spec B a b "x" "y" "x" hB

-- Existing automaton computability crosses the semantic front end unchanged.
-- The source convention is unchanged by the execution bridge.
example : ∃ c : Code, ∀ n : Nat,
    c.eval n = Encodable.encode
      ((Encodable.decode (α := Lax53.ValueTranslations.RankedAlphabetCode ×
        Lax53.ValueTranslations.AutomatonCode ×
        Lax53.ValueTranslations.AutomatonCode) n).map
          (fun x => Lax53Proofs.EncodedAutomataOperations.inter x.1 x.2.1 x.2.2)) :=
  exists_typed_code Lax53Proofs.EncodedAutomataComputability.inter_prim

/-- info: 'Lax53Proofs.PrimitiveRecursiveCode.exists_typed_code' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_typed_code

/-- info: 'Lax53Proofs.PrimitiveRecursivePairing.unpairLeft_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpairLeft_spec

/-- info: 'Lax53Proofs.PrimitiveRecursivePairing.unpairRight_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unpairRight_spec

/-- info: 'Lax53Proofs.PrimitiveRecursiveCompile.compile_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_frame

/-- info: 'Lax53Proofs.PrimitiveRecursiveBounds.budget_prim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms budget_prim

/-- info: 'Lax53Proofs.PrimitiveRecursiveBounds.eval_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_le_budget

/-- info: 'Lax53Proofs.PrimitiveRecursiveCorrectness.correct_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms correct_pair

/-- info: 'Lax53Proofs.PrimitiveRecursiveCorrectness.compile_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms compile_correct

/-- info: 'Lax53Proofs.PrimitiveRecursiveRam.exists_typed_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.PrimitiveRecursiveRam.exists_typed_ram

/-- info: 'Lax53Proofs.PrimitiveRecursiveAutomata.inter_ram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.PrimitiveRecursiveAutomata.inter_ram
