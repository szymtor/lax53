import Mathlib.Data.Fintype.Powerset
import Lax53.Determinization

namespace Lax53Proofs.Determinization

open Lax53.RankedTree
open Lax53.TreeAutomaton

universe u v

variable {A : RankedAlphabet.{u}} {Q : Type v} [Fintype Q]

/-- The set of possible parent states above a symbol and sets of possible
states at its children. -/
noncomputable def step (M : Automaton A Q) (a : A.Symbol)
    (childStates : Fin (A.rank a) → Finset Q) : Finset Q := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ qs : Fin (A.rank a) → Q,
      M.transition a q qs = true ∧ ∀ i, qs i ∈ childStates i

@[simp]
theorem mem_step (M : Automaton A Q) (a : A.Symbol)
    (childStates : Fin (A.rank a) → Finset Q) (q : Q) :
    q ∈ step M a childStates ↔
      ∃ qs : Fin (A.rank a) → Q,
        M.transition a q qs = true ∧ ∀ i, qs i ∈ childStates i := by
  classical
  simp [step]

/-- The finite set of all states to which `M` can run on a tree. -/
noncomputable def eval (M : Automaton A Q) : Tree A → Finset Q
  | .node a children => step M a (fun i => eval M (children i))

@[simp]
theorem mem_eval_iff_runsTo (M : Automaton A Q) (t : Tree A) (q : Q) :
    q ∈ eval M t ↔ M.RunsTo t q := by
  classical
  induction t generalizing q with
  | node a children ih =>
      simp only [eval, mem_step, Automaton.RunsTo]
      constructor
      · rintro ⟨qs, htrans, hchildren⟩
        exact ⟨qs, htrans, fun i => (ih i (qs i)).mp (hchildren i)⟩
      · rintro ⟨qs, htrans, hchildren⟩
        exact ⟨qs, htrans, fun i => (ih i (qs i)).mpr (hchildren i)⟩

/-- The deterministic subset automaton. -/
noncomputable def determinize (M : Automaton A Q) : Automaton A (Finset Q) := by
  classical
  exact
    { transition := fun a parent childStates => decide (parent = step M a childStates)
      accept := fun states => decide (∃ q ∈ states, M.accept q = true) }

theorem determinize_deterministic (M : Automaton A Q) :
    (determinize M).Deterministic := by
  classical
  intro a childStates
  refine ⟨step M a childStates, by simp [determinize], ?_⟩
  intro states hstates
  simpa [determinize] using hstates

@[simp]
theorem determinize_runsTo_iff (M : Automaton A Q) (t : Tree A)
    (states : Finset Q) :
    (determinize M).RunsTo t states ↔ states = eval M t := by
  classical
  induction t generalizing states with
  | node a children ih =>
      constructor
      · rintro ⟨childStates, hstep, hruns⟩
        have hparent : states = step M a childStates := by
          simpa [determinize] using hstep
        have hchildren : childStates = fun i => eval M (children i) := by
          funext i
          exact (ih i (childStates i)).mp (hruns i)
        simpa [eval, hchildren] using hparent
      · intro hstates
        subst states
        refine ⟨fun i => eval M (children i), ?_, ?_⟩
        · simp [determinize, eval]
        · intro i
          exact (ih i (eval M (children i))).mpr rfl

theorem determinize_accepts_iff (M : Automaton A Q) (t : Tree A) :
    (determinize M).Accepts t ↔ M.Accepts t := by
  classical
  constructor
  · rintro ⟨states, haccept, hrun⟩
    have haccept' : ∃ q ∈ states, M.accept q = true := by
      simpa [determinize] using haccept
    have hstates := (determinize_runsTo_iff M t states).mp hrun
    obtain ⟨q, hqstates, hqaccept⟩ := haccept'
    refine ⟨q, hqaccept, ?_⟩
    exact (mem_eval_iff_runsTo M t q).mp (hstates ▸ hqstates)
  · rintro ⟨q, hqaccept, hqrun⟩
    refine ⟨eval M t, ?_, (determinize_runsTo_iff M t _).mpr rfl⟩
    change decide (∃ r ∈ eval M t, M.accept r = true) = true
    simp only [decide_eq_true_eq]
    exact ⟨q, (mem_eval_iff_runsTo M t q).mpr hqrun, hqaccept⟩

/--
---
conclusion: Lax53.Determinization.exists_deterministic_equivalent
---
-/
theorem exists_deterministic_equivalent_proof {A : RankedAlphabet.{u}} {Q : Type v}
    [Fintype Q] (M : Automaton A Q) :
    ∃ Q' : Type v, ∃ _ : Fintype Q', ∃ D : Automaton A Q',
      D.Deterministic ∧ D.language = M.language := by
  classical
  refine ⟨Finset Q, inferInstance, determinize M, determinize_deterministic M, ?_⟩
  ext t
  exact determinize_accepts_iff M t

end Lax53Proofs.Determinization
