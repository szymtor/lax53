import Mathlib.Data.Fintype.Prod
import Lax53Proofs.Determinization

namespace Lax53Proofs.TreeAutomataClosure

open Lax53.RankedTree
open Lax53.TreeAutomaton

universe u v w

variable {A : RankedAlphabet.{u}}

/-- An automaton accepting no trees. -/
def emptyAutomaton : Automaton A Unit where
  transition _ _ _ := true
  accept _ := false

theorem emptyAutomaton_runsTo (t : Tree A) : emptyAutomaton.RunsTo t () := by
  induction t with
  | node a children ih => exact ⟨fun _ => (), rfl, ih⟩

theorem recognizable_empty : Recognizable (A := A) ∅ := by
  refine ⟨Unit, inferInstance, emptyAutomaton, ?_⟩
  ext t
  simp [Automaton.language, Automaton.Accepts, emptyAutomaton]

/-- Synchronous product of two bottom-up tree automata. -/
def product {Q : Type v} {R : Type w} (M : Automaton A Q) (N : Automaton A R) :
    Automaton A (Q × R) where
  transition a qr children :=
    M.transition a qr.1 (fun i => (children i).1) &&
      N.transition a qr.2 (fun i => (children i).2)
  accept qr := M.accept qr.1 && N.accept qr.2

theorem product_runsTo_iff {Q : Type v} {R : Type w}
    (M : Automaton A Q) (N : Automaton A R) (t : Tree A) (q : Q) (r : R) :
    (product M N).RunsTo t (q, r) ↔ M.RunsTo t q ∧ N.RunsTo t r := by
  induction t generalizing q r with
  | node a children ih =>
      constructor
      · rintro ⟨states, hstep, hruns⟩
        have hstep' := Bool.and_eq_true_iff.mp hstep
        refine ⟨⟨fun i => (states i).1, hstep'.1, ?_⟩,
          ⟨fun i => (states i).2, hstep'.2, ?_⟩⟩
        · intro i
          exact (ih i _ _).mp (hruns i) |>.1
        · intro i
          exact (ih i _ _).mp (hruns i) |>.2
      · rintro ⟨⟨qs, hM, hrunsM⟩, ⟨rs, hN, hrunsN⟩⟩
        refine ⟨fun i => (qs i, rs i), Bool.and_eq_true_iff.mpr ⟨hM, hN⟩, ?_⟩
        intro i
        exact (ih i _ _).mpr ⟨hrunsM i, hrunsN i⟩

theorem product_accepts_iff {Q : Type v} {R : Type w}
    (M : Automaton A Q) (N : Automaton A R) (t : Tree A) :
    (product M N).Accepts t ↔ M.Accepts t ∧ N.Accepts t := by
  constructor
  · rintro ⟨⟨q, r⟩, haccept, hrun⟩
    have ha := Bool.and_eq_true_iff.mp haccept
    have hr := (product_runsTo_iff M N t q r).mp hrun
    exact ⟨⟨q, ha.1, hr.1⟩, ⟨r, ha.2, hr.2⟩⟩
  · rintro ⟨⟨q, hq, hrunq⟩, ⟨r, hr, hrunr⟩⟩
    exact ⟨(q, r), Bool.and_eq_true_iff.mpr ⟨hq, hr⟩,
      (product_runsTo_iff M N t q r).mpr ⟨hrunq, hrunr⟩⟩

theorem recognizable_intersection (L K : TreeLanguage A)
    (hL : Recognizable L) (hK : Recognizable K) :
    Recognizable (L ∩ K) := by
  rcases hL with ⟨Q, hQ, M, rfl⟩
  rcases hK with ⟨R, hR, N, rfl⟩
  letI := hQ
  letI := hR
  refine ⟨Q × R, inferInstance, product M N, ?_⟩
  ext t
  exact product_accepts_iff M N t

/-- Change only the accepting test. -/
def flipAccept {Q : Type v} (M : Automaton A Q) : Automaton A Q where
  transition := M.transition
  accept q := !(M.accept q)

theorem flipAccept_runsTo_iff {Q : Type v} (M : Automaton A Q)
    (t : Tree A) (q : Q) :
    (flipAccept M).RunsTo t q ↔ M.RunsTo t q := by
  induction t generalizing q with
  | node a children ih =>
      constructor
      · rintro ⟨states, hstep, hruns⟩
        exact ⟨states, hstep, fun i => (ih i _).mp (hruns i)⟩
      · rintro ⟨states, hstep, hruns⟩
        exact ⟨states, hstep, fun i => (ih i _).mpr (hruns i)⟩

/-- A total deterministic automaton has exactly one run state on every tree. -/
theorem deterministic_exists_unique_run {Q : Type v} (M : Automaton A Q)
    (hM : M.Deterministic) (t : Tree A) : ∃! q : Q, M.RunsTo t q := by
  induction t with
  | node a children ih =>
      choose childStates hchildren hchildUnique using ih
      obtain ⟨q, hstep, hqUnique⟩ := hM a childStates
      refine ⟨q, ⟨childStates, hstep, hchildren⟩, ?_⟩
      intro r hr
      rcases hr with ⟨otherStates, hotherStep, hotherRuns⟩
      have hstates : otherStates = childStates := by
        funext i
        exact hchildUnique i (otherStates i) (hotherRuns i)
      subst otherStates
      exact hqUnique r hotherStep

theorem flipAccept_accepts_iff_not {Q : Type v} (M : Automaton A Q)
    (hM : M.Deterministic) (t : Tree A) :
    (flipAccept M).Accepts t ↔ ¬M.Accepts t := by
  obtain ⟨q, hq, hunique⟩ := deterministic_exists_unique_run M hM t
  constructor
  · rintro ⟨r, hrAccept, hrRun⟩ haccept
    rcases haccept with ⟨s, hsAccept, hsRun⟩
    have hrs : r = s := (hunique r ((flipAccept_runsTo_iff M t r).mp hrRun)).trans
      (hunique s hsRun).symm
    subst s
    simp [flipAccept, hsAccept] at hrAccept
  · intro hnot
    refine ⟨q, ?_, (flipAccept_runsTo_iff M t q).mpr hq⟩
    have hfalse : M.accept q = false := by
      cases h : M.accept q with
      | false => rfl
      | true => exact False.elim (hnot ⟨q, h, hq⟩)
    simp [flipAccept, hfalse]

theorem recognizable_complement (L : TreeLanguage A) (hL : Recognizable L) :
    Recognizable {t | t ∉ L} := by
  rcases hL with ⟨Q, hQ, M, hML⟩
  letI := hQ
  let D := Lax53Proofs.Determinization.determinize M
  refine ⟨Finset Q, inferInstance, flipAccept D, ?_⟩
  ext t
  change (flipAccept D).Accepts t ↔ t ∉ L
  rw [flipAccept_accepts_iff_not D
    (Lax53Proofs.Determinization.determinize_deterministic M)]
  rw [Lax53Proofs.Determinization.determinize_accepts_iff]
  change ¬ t ∈ M.language ↔ t ∉ L
  rw [hML]

theorem recognizable_union (L K : TreeLanguage A)
    (hL : Recognizable L) (hK : Recognizable K) :
    Recognizable (L ∪ K) := by
  have hcL := recognizable_complement L hL
  have hcK := recognizable_complement K hK
  have hi := recognizable_intersection {t | t ∉ L} {t | t ∉ K} hcL hcK
  have hc := recognizable_complement ({t | t ∉ L} ∩ {t | t ∉ K}) hi
  simpa only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, not_and_or,
    Classical.not_not] using hc

end Lax53Proofs.TreeAutomataClosure
