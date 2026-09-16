import Lax842588Proofs.IntrinsicCompilerFromArena

/-! The measured compiler preserves the original arena and its tree pointer. -/

namespace Lax842588Proofs.IntrinsicCompilerFrame

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning
open Lax842588Proofs.PrimitiveRecursiveCode Lax842588Proofs.PrimitiveRecursiveCompile
open Lax842588Proofs.PrimitiveRecursivePairing Lax842588Proofs.IntrinsicCompilerFromArena
open Lax842588Proofs.AutomatonRamArenaCorrectness Lax560851.WordArena

theorem compile_keeps (c : Code) (d : Nat) (s : String) (hs : ∀ j, s ≠ reg j) :
    s ∉ (compile c d).wvars := by
  induction c generalizing d <;>
    simp_all [compile, copy, recursionStep, pairProgram, unpairLeftProgram,
      unpairRightProgram, sqrtProgram, sqrtLoop, sqrtStep, Com.wvars]

theorem arena_names_fresh (s : String) (hs : s ∈ ["root", "arenaLen", "treeRoot"]) :
    ∀ j, s ≠ reg j := by
  intro j heq
  have hr : ∀ ch ∈ s.toList, ch = 'r' := by
    rw [heq]
    simp [reg]
  simp at hs
  rcases hs with rfl | rfl | rfl
  · have := hr 'o' (by decide); contradiction
  · have := hr 'a' (by decide); contradiction
  · have := hr 't' (by decide); contradiction

theorem program_keeps (c : Code) (s : String)
    (hs : s ∈ ["root", "arenaLen", "treeRoot"]) : s ∉ (program c).wvars := by
  have hc := compile_keeps c 0 s (arena_names_fresh s hs)
  have hi : s ∉ inputProgram.wvars := by
    simp at hs
    rcases hs with rfl | rfl | rfl <;> decide
  have hu : s ∉ (CompilerArrayUnpacking.program "P").wvars := by
    simp at hs
    rcases hs with rfl | rfl | rfl <;> decide
  have hn : s ≠ "unpackCode" := by
    simp at hs
    rcases hs with rfl | rfl | rfl <;> decide
  simp [program, IntrinsicCompilerMaterialize.materialize, Com.wvars, hi, hc, hu, hn]

theorem preserves_arena {B K : Nat} {c : Code} {I : WordImage} {σ τ : Env}
    (h : Run B (program c) σ τ K) (ha : ArenaLoaded I σ) : ArenaLoaded I τ := by
  rcases ha with ⟨ha, hr, hl, hi⟩
  exact ⟨(h.frame_arr "Arena" (by simp)).trans ha,
    (h.frame_var "root" (program_keeps c _ (by simp))).trans hr,
    (h.frame_var "arenaLen" (program_keeps c _ (by simp))).trans hl,
    (h.frame_inp (program_noRead c)).trans hi⟩

end Lax842588Proofs.IntrinsicCompilerFrame
