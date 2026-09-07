import Lax13Proofs.Reasoning
import Lax13Proofs.Spec

/-!
Local operational bookkeeping for the structural frontend. IMP+ has no array
allocation command: stores update cells in place, so every run preserves the
length of every array. Keeping this proof local avoids exposing implementation
infrastructure in either concept package.
-/

namespace Lax53Proofs

open Lax13Proofs.Imp
open Lax13Proofs.Reasoning

theorem bigStepB_arrayLength_eq {B : Nat} {command : Com} {sigma sigma' : Env}
    {cost : Nat} (run : BigStepB B command sigma sigma' cost) (array : String) :
    (sigma'.arrs array).length = (sigma.arrs array).length := by
  induction run with
  | skip => rfl
  | assign _ => simp
  | store _ _ _ => exact length_arrs_setArr _ _ _ _ _
  | seq _ _ first second => exact second.trans first
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ body loop => exact loop.trans body
  | while_false _ => rfl
  | read _ => simp
  | write _ => rfl

theorem Run.arrayLength_eq {B : Nat} {command : Com} {sigma sigma' : Env}
    {cost : Nat} (run : Run B command sigma sigma' cost) (array : String) :
    (sigma'.arrs array).length = (sigma.arrs array).length := by
  obtain ⟨_, _, bigStep⟩ := run
  exact bigStepB_arrayLength_eq bigStep array

/-- Array-length analogue of the ordinary frame rule. Every IMP+ command
preserves every array's extent, including arrays into which it stores. -/
theorem spec_arrayLength_eq {B : Nat} {P : Env → Prop} {command : Com}
    {Q : Env → Env → Prop} {cost : Nat}
    (spec : Spec B P command Q cost) (array : String) :
    Spec B P command
      (fun sigma sigma' => Q sigma sigma' ∧
        (sigma'.arrs array).length = (sigma.arrs array).length)
      cost := by
  intro sigma hpre
  obtain ⟨sigma', run, hpost⟩ := spec.run hpre
  exact ⟨sigma', run, hpost, Run.arrayLength_eq run array⟩

end Lax53Proofs
