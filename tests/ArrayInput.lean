import Lax53Proofs.ArrayInput

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax53Proofs.ArrayInput

-- The localized reader is exactly the original Lax13 command syntax.
example (a x m tmp : String) : readArr a x m tmp =
    Com.seq (.assign x (.lit 0))
      (.while (.lt (.var x) (.var m)) (.seq (.read tmp) (Fill.put a x (.var tmp)))) := rfl

-- Empty input preserves the unread suffix and still charges initialization.
example (rest : List Nat) :
    Spec 16 (fun σ => (σ.arrs "A").length = 0 ∧ σ.vars "n" = 0 ∧ σ.inp = rest)
      (readArr "A" "i" "n" "tmp")
      (fun _ σ' => σ'.arrs "A" = [] ∧ σ'.inp = rest ∧ σ'.vars "i" = 0) 6 := by
  simpa using readArr_spec 16 "A" "i" "n" "tmp" [] rest
    (by decide) (by decide) (by decide) (by decide) (by simp)

-- Three entries retain their order; the suffix is not consumed. Cost: 12*3+6.
example (rest : List Nat) :
    Spec 16 (fun σ => (σ.arrs "A").length = 3 ∧ σ.vars "n" = 3 ∧
        σ.inp = [5, 6, 7] ++ rest)
      (readArr "A" "i" "n" "tmp")
      (fun _ σ' => σ'.arrs "A" = [5, 6, 7] ∧ σ'.inp = rest ∧ σ'.vars "i" = 3) 42 := by
  simpa using readArr_spec 16 "A" "i" "n" "tmp" [5, 6, 7] rest
    (by decide) (by decide) (by decide) (by decide) (by simp)

example (a x m tmp : String) : (readArr a x m tmp).NoWrite := by simp
example (a x m tmp : String) : (readArr a x m tmp).warrs = [a] := by simp
example (a x m tmp : String) : (readArr a x m tmp).wvars = [x, tmp, x] := by simp

/-- info: 'Lax53Proofs.ArrayInput.readArr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax53Proofs.ArrayInput.readArr_spec
