import Lax842588Proofs.AutomatonRamEvaluateTree

/-! Recover evaluator fields from the runtime-built table, without tape I/O. -/

namespace Lax842588Proofs.IntrinsicEvaluatorHeader

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning Lax865980Proofs.Compile
open Lax842588.ValueTranslations Lax842588.TreeModelCheckingEncoding
open Lax842588Proofs.AutomatonRamCorrectness Lax842588Proofs.AutomatonTableEncoding

def program : Com := AutomatonRamProgram.seqs [
  .assign "A" (.get "P" (.lit 0)),
  .assign "Q" (.get "P" (.add (.var "A") (.lit 1))),
  .assign "T" (.get "P" (.add (.var "A") (.lit 2))),
  .assign "R" (.get "P" (.add (.var "A") (.lit 3))),
  .assign "width" (.add (.var "R") (.lit 3)),
  .assign "records" (.add (.var "A") (.lit 4)),
  .assign "acceptBase" (.add (.var "records") (.mul (.var "T") (.var "width"))),
  .assign "F" (.get "P" (.var "acceptBase"))]

set_option maxHeartbeats 3000000 in
theorem program_spec (B : Nat) (M : EncodedAutomaton) (n : Nat)
    (h0 : 0 < B) (hparam : ∀ v ∈ encodeAutomaton M, v < B)
    (hwork : M.1.length + M.2.1 + M.2.2.1.length + maximumRank M.1 +
      M.2.2.1.length * (maximumRank M.1 + 3) + M.2.2.2.length + n + 20 < B) :
    Spec B (fun σ => σ.arrs "P" = encodeAutomaton M ∧ σ.vars "n" = n) program
      (fun _ σ => EvalFields M n σ) 100 := by
  intro σ hσ
  have hget (i : Nat) : (encodeAutomaton M).getD i 0 < B :=
    getD_lt_of_mem_bound h0 hparam
  have hA := encodeAutomaton_A M
  have hQ := encodeAutomaton_Q M
  have hT := encodeAutomaton_T M
  have hR := encodeAutomaton_R M
  have hF := encodeAutomaton_acceptCount M
  unfold program AutomatonRamProgram.seqs
  run_vcg
  all_goals simp_all [EvalFields, encodeAutomaton_length]
  all_goals try exact hget _
  all_goals omega

@[simp] theorem program_warrs : program.warrs = [] := by decide
theorem program_noRead : ¬ program.reads := by decide
theorem program_noWrite : program.NoWrite := by decide

def scalars : List String := ["A", "Q", "T", "R", "width", "records", "acceptBase", "F"]

theorem program_ok (L : Layout) (ht : 5 ≤ L.temps) (hp : "P" ∈ L.arrays)
    (hs : ∀ s ∈ scalars, s ∈ L.scalars) : Com.Ok L program := by
  simp only [scalars, List.forall_mem_cons] at hs
  rcases hs with ⟨hA, hQ, hT, hR, hw, hr, hb, hF⟩
  simp [program, AutomatonRamProgram.seqs, Com.Ok, Expr.Ok,
    hp, hA, hQ, hT, hR, hw, hr, hb, hF]
  omega

end Lax842588Proofs.IntrinsicEvaluatorHeader
