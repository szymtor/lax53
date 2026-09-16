import Lax842588Proofs.IntrinsicCompilerParameters
import Lax842588Proofs.IntrinsicCompiledTableBounds
import Lax842588Proofs.IntrinsicInputBounds

/-! Parameter-only coefficients for the complete measured model-checking run. -/

namespace Lax842588Proofs.IntrinsicTimeBounds

open Lax759944Proofs.Legacy.Imp
open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.MSOLinearTime Lax842588.TreeModelCheckingEncoding Lax560851.WordArena
open Lax842588Proofs.IntrinsicParameterEncoding Lax842588Proofs.IntrinsicCompilerParameters
open Lax842588Proofs.IntrinsicCompiledTableBounds Lax842588Proofs.IntrinsicInputBounds
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.AutomatonRamCorrectness
open Lax842588Proofs.AutomatonRamBackend
open Lax842588Proofs.AutomatonRamArenaCorrectness Lax842588Proofs.AutomatonRamArenaReadTree
open Lax842588Proofs.AutomatonRamArenaTreeLoop Lax842588Proofs.AutomatonRamArenaTreeInvariant

def compilerTime (c : Code) (p : Nat) : Nat :=
  4000 * (fieldBound p + 1) + 150 * (headerCodeBound p + fieldBound p + 2) +
    materializeTime c p

theorem compilerTime_prim (c : Code) : Primrec (compilerTime c) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4000)
      (Primrec.nat_add.comp fieldBound_prim (Primrec.const 1)))
    (Primrec.nat_mul.comp (Primrec.const 150)
      (Primrec.nat_add.comp (Primrec.nat_add.comp headerCodeBound_prim fieldBound_prim)
        (Primrec.const 2)))) (materializeTime_prim c)

theorem public_time_le (c : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    IntrinsicPublicCompiler.timeBound c alphabet φ t ≤
      12 * (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords +
        compilerTime c (parameterSize alphabet φ) := by
  have ha := (shape_bounds alphabet φ).alphabetLength
  have hs := (shape_bounds alphabet φ).steps
  have hn := (shape_bounds alphabet φ).count
  have hh := header_code_le alphabet φ
  have hc := materialize_time_le c alphabet φ
  simp only [IntrinsicPublicCompiler.timeBound, IntrinsicCompilerPrepare.timeBound,
    IntrinsicCompilerFromArena.inputTime, IntrinsicAlphabetInput.timeBound,
    alphabetLoopCost, AutomatonRamArenaProgram.alphabetCondition,
    FormulaArenaTraversalRead.formulaReadCost,
    FormulaArenaTraversalLoop.formulaTraversalLoopCost,
    FormulaArenaTraversalLoop.formulaLoopCondition, Cond.size, Expr.size, compilerTime]
  omega

theorem prepare_time_le (M : EncodedAutomaton) (t : Tree M.1.toRankedAlphabet) :
    IntrinsicEvaluatorPrepare.timeBound M t ≤ 1000 * (treeSize t + 1) := by
  simp only [IntrinsicEvaluatorPrepare.timeBound, readTreeCost, treeTraversalLoopCost,
    treeLoopCondition, Cond.size, Expr.size]
  omega

theorem backend_time_le (M : EncodedAutomaton) (H : Nat) (h : TableBounds M H)
    (t : Tree M.1.toRankedAlphabet) :
    automatonBackendCost M t ≤ 1000 * (H + 1) ^ 2 * (treeSize t + 1) := by
  have hT := h.transitions
  have hF := h.accepting
  have hrank := rankSum_encodeTree_add_one M.1 t
  let n := treeSize t
  let T := M.2.2.1.length
  let F := M.2.2.2.length
  have hmeasure : n + rankSum M.1 (encodeTree M.1 t) ≤ 2 * n := by
    dsimp [n]
    omega
  have hsq : (T + 1) ^ 2 ≤ (H + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hnode : 300 * (T + 1) ^ 2 * (n + rankSum M.1 (encodeTree M.1 t)) ≤
      600 * (H + 1) ^ 2 * n := by
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 300 hsq) hmeasure
    nlinarith
  have hFT : F * T ≤ H * H := Nat.mul_le_mul hF hT
  have hrest : (39 * F + 34) * T + 51 ≤ 100 * (H + 1) ^ 2 * (n + 1) := by
    dsimp [n, T, F] at hFT ⊢
    nlinarith [sq_nonneg (H : Int)]
  unfold automatonBackendCost nodeCoefficient
  dsimp [n, T, F] at hnode hrest
  nlinarith

def impTimeCoefficient (c d : Code) (p : Nat) : Nat :=
  36 * (p + 6) + compilerTime c p + 1000 + 1000 * (tableAllowance d p + 1) ^ 2

theorem impTimeCoefficient_prim (c d : Code) : Primrec (impTimeCoefficient c d) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 36)
      (Primrec.nat_add.comp Primrec.id (Primrec.const 6)))
    (compilerTime_prim c)) (Primrec.const 1000))
    (Primrec.nat_mul.comp (Primrec.const 1000)
      (pow_prim.comp (Primrec.nat_add.comp (tableAllowance_prim d) (Primrec.const 1))
        (Primrec.const 2)))

theorem time_le (c d : Code) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (h : TableBounds (IntrinsicModelChecking.compiled alphabet φ)
      (tableAllowance d (parameterSize alphabet φ)))
    (t : Tree alphabet.toRankedAlphabet) :
    IntrinsicModelChecking.timeBound c alphabet φ t ≤
      impTimeCoefficient c d (parameterSize alphabet φ) * (treeSize t + 1) := by
  have hc := public_time_le c alphabet φ t
  have hp := prepare_time_le (IntrinsicModelChecking.compiled alphabet φ) t
  have hb := backend_time_le _ _ h t
  have hi := input_size_le alphabet φ t
  rw [arena_memory] at hc
  unfold IntrinsicModelChecking.timeBound
  calc
    _ ≤ (36 * (parameterSize alphabet φ + 6) * (treeSize t + 1) +
          compilerTime c (parameterSize alphabet φ) * (treeSize t + 1)) +
        (1000 * (treeSize t + 1) +
          1000 * (tableAllowance d (parameterSize alphabet φ) + 1) ^ 2 * (treeSize t + 1)) := by
      apply Nat.add_le_add _ (Nat.add_le_add hp hb)
      apply hc.trans
      apply Nat.add_le_add
      · nlinarith only [hi]
      · exact Nat.le_mul_of_pos_right _ (by omega)
    _ = _ := by unfold impTimeCoefficient; ring

end Lax842588Proofs.IntrinsicTimeBounds
