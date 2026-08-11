import Lax53Proofs.MarkedTrees

namespace Lax53Proofs.MarkerProjection

open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53Proofs.MarkedTrees

universe u v

noncomputable def projectFO {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A (n + 1) m) Q) :
    Automaton (MarkedAlphabet A n m) Q := by
  classical
  exact
    { transition := fun s q children =>
        decide (∃ bit : Bool, M.transition (MarkedAlphabet.liftFO s bit) q children = true)
      accept := M.accept }

noncomputable def projectSO {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A n (m + 1)) Q) :
    Automaton (MarkedAlphabet A n m) Q := by
  classical
  exact
    { transition := fun s q children =>
        decide (∃ bit : Bool, M.transition (MarkedAlphabet.liftSO s bit) q children = true)
      accept := M.accept }

theorem projectFO_runsTo_of {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A (n + 1) m) Q)
    (t : Tree (MarkedAlphabet A (n + 1) m)) (q : Q)
    (h : M.RunsTo t q) : (projectFO M).RunsTo (dropFOTree t) q := by
  classical
  induction t generalizing q with
  | node s children ih =>
      rcases h with ⟨states, hstep, hruns⟩
      refine ⟨states, ?_, fun i => ih i (states i) (hruns i)⟩
      change decide (∃ bit : Bool,
        M.transition (MarkedAlphabet.liftFO (MarkedAlphabet.dropFO s) bit) q states = true) = true
      simp only [decide_eq_true_eq]
      refine ⟨s.2.1 0, ?_⟩
      rcases s with ⟨a, fo, so⟩
      change M.transition (a, Fin.cases (fo 0) (fun x => fo x.succ), so) q states = true
      have hfo : Fin.cases (fo 0) (fun x => fo x.succ) = fo := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hfo]
      exact hstep

theorem projectSO_runsTo_of {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A n (m + 1)) Q)
    (t : Tree (MarkedAlphabet A n (m + 1))) (q : Q)
    (h : M.RunsTo t q) : (projectSO M).RunsTo (dropSOTree t) q := by
  classical
  induction t generalizing q with
  | node s children ih =>
      rcases h with ⟨states, hstep, hruns⟩
      refine ⟨states, ?_, fun i => ih i (states i) (hruns i)⟩
      change decide (∃ bit : Bool,
        M.transition (MarkedAlphabet.liftSO (MarkedAlphabet.dropSO s) bit) q states = true) = true
      simp only [decide_eq_true_eq]
      refine ⟨s.2.2 0, ?_⟩
      rcases s with ⟨a, fo, so⟩
      change M.transition (a, fo, Fin.cases (so 0) (fun X => so X.succ)) q states = true
      have hso : Fin.cases (so 0) (fun X => so X.succ) = so := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      rw [hso]
      exact hstep

theorem exists_of_projectFO_runsTo {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A (n + 1) m) Q)
    (t : Tree (MarkedAlphabet A n m)) (q : Q)
    (h : (projectFO M).RunsTo t q) :
    ∃ source : Tree (MarkedAlphabet A (n + 1) m),
      dropFOTree source = t ∧ M.RunsTo source q := by
  classical
  induction t generalizing q with
  | node s children ih =>
      rcases h with ⟨states, hstep, hruns⟩
      change decide (∃ bit : Bool,
        M.transition (MarkedAlphabet.liftFO s bit) q states = true) = true at hstep
      obtain ⟨bit, htransition⟩ := of_decide_eq_true hstep
      have hwitness : ∀ i, ∃ source,
          dropFOTree source = children i ∧ M.RunsTo source (states i) :=
        fun i => ih i (states i) (hruns i)
      choose sourceChildren hdrops hrunsSource using hwitness
      refine ⟨.node (MarkedAlphabet.liftFO s bit) sourceChildren, ?_,
        ⟨states, htransition, hrunsSource⟩⟩
      simp only [dropFOTree, MarkedAlphabet.dropFO_liftFO, Tree.node.injEq,
        true_and]
      exact heq_of_eq (funext hdrops)

theorem exists_of_projectSO_runsTo {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A n (m + 1)) Q)
    (t : Tree (MarkedAlphabet A n m)) (q : Q)
    (h : (projectSO M).RunsTo t q) :
    ∃ source : Tree (MarkedAlphabet A n (m + 1)),
      dropSOTree source = t ∧ M.RunsTo source q := by
  classical
  induction t generalizing q with
  | node s children ih =>
      rcases h with ⟨states, hstep, hruns⟩
      change decide (∃ bit : Bool,
        M.transition (MarkedAlphabet.liftSO s bit) q states = true) = true at hstep
      obtain ⟨bit, htransition⟩ := of_decide_eq_true hstep
      have hwitness : ∀ i, ∃ source,
          dropSOTree source = children i ∧ M.RunsTo source (states i) :=
        fun i => ih i (states i) (hruns i)
      choose sourceChildren hdrops hrunsSource using hwitness
      refine ⟨.node (MarkedAlphabet.liftSO s bit) sourceChildren, ?_,
        ⟨states, htransition, hrunsSource⟩⟩
      simp only [dropSOTree, MarkedAlphabet.dropSO_liftSO, Tree.node.injEq,
        true_and]
      exact heq_of_eq (funext hdrops)

theorem projectFO_accepts_iff {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A (n + 1) m) Q)
    (t : Tree (MarkedAlphabet A n m)) :
    (projectFO M).Accepts t ↔
      ∃ source, dropFOTree source = t ∧ M.Accepts source := by
  constructor
  · rintro ⟨q, haccept, hrun⟩
    obtain ⟨source, hdrop, hrunSource⟩ := exists_of_projectFO_runsTo M t q hrun
    exact ⟨source, hdrop, q, haccept, hrunSource⟩
  · rintro ⟨source, rfl, q, haccept, hrun⟩
    exact ⟨q, haccept, projectFO_runsTo_of M source q hrun⟩

theorem projectSO_accepts_iff {A : RankedAlphabet.{u}} {n m : Nat} {Q : Type v}
    (M : Automaton (MarkedAlphabet A n (m + 1)) Q)
    (t : Tree (MarkedAlphabet A n m)) :
    (projectSO M).Accepts t ↔
      ∃ source, dropSOTree source = t ∧ M.Accepts source := by
  constructor
  · rintro ⟨q, haccept, hrun⟩
    obtain ⟨source, hdrop, hrunSource⟩ := exists_of_projectSO_runsTo M t q hrun
    exact ⟨source, hdrop, q, haccept, hrunSource⟩
  · rintro ⟨source, rfl, q, haccept, hrun⟩
    exact ⟨q, haccept, projectSO_runsTo_of M source q hrun⟩

end Lax53Proofs.MarkerProjection
