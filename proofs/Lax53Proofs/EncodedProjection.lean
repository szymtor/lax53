import Lax53Proofs.EncodedAutomataOperations

namespace Lax53Proofs.EncodedProjection

open Lax53.ValueTranslations
open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53Proofs.EncodedAutomataOperations

/-- Relabel a tree along a rank-preserving map between arbitrary ranked
alphabets. -/
def relabelTree {A B : RankedAlphabet}
    (symbolMap : A.Symbol → B.Symbol)
    (rankMap : ∀ a, B.rank (symbolMap a) = A.rank a) : Tree A → Tree B
  | .node a children =>
      .node (symbolMap a) fun i =>
        relabelTree symbolMap rankMap (children (Fin.cast (rankMap a) i))

theorem relabelTree_comp {A B C : RankedAlphabet}
    (f : A.Symbol → B.Symbol) (hf : ∀ a, B.rank (f a) = A.rank a)
    (g : B.Symbol → C.Symbol) (hg : ∀ b, C.rank (g b) = B.rank b)
    (t : Tree A) :
    relabelTree g hg (relabelTree f hf t) =
      relabelTree (g ∘ f) (fun a => (hg (f a)).trans (hf a)) t := by
  induction t with
  | node a children ih =>
      simp only [relabelTree, Function.comp_apply]
      congr 1
      funext i
      simpa using ih (Fin.cast ((hg (f a)).trans (hf a)) i)

theorem relabelTree_congr {A B : RankedAlphabet}
    {f g : A.Symbol → B.Symbol}
    (hfg : f = g)
    (hf : ∀ a, B.rank (f a) = A.rank a)
    (hg : ∀ a, B.rank (g a) = A.rank a)
    (t : Tree A) :
    relabelTree f hf t = relabelTree g hg t := by
  subst g
  have hrank : hf = hg := Subsingleton.elim _ _
  subst hrank
  rfl

theorem relabelTree_id {A : RankedAlphabet} (t : Tree A) :
    relabelTree id (fun _ => rfl) t = t := by
  induction t with
  | node a children ih =>
      simp only [relabelTree, id_eq]
      exact congrArg (Tree.node a) (funext ih)

theorem relabelTree_equiv_inverse {A B : RankedAlphabet}
    (e : A.Symbol ≃ B.Symbol)
    (h : ∀ a, B.rank (e a) = A.rank a)
    (h' : ∀ b, A.rank (e.symm b) = B.rank b)
    (t : Tree A) :
    relabelTree e.symm h' (relabelTree e h t) = t := by
  rw [relabelTree_comp]
  calc
    _ = relabelTree id (fun _ => rfl) t := relabelTree_congr
      (funext e.symm_apply_apply) _ _ t
    _ = t := relabelTree_id t

/-- Generic run transport along simultaneous symbol and state equivalences. -/
theorem relabelTree_runsTo_iff {A B : RankedAlphabet} {Q R : Type*}
    (symbolMap : A.Symbol → B.Symbol)
    (rankMap : ∀ a, B.rank (symbolMap a) = A.rank a)
    (stateEquiv : Q ≃ R) (M : Automaton A Q) (N : Automaton B R)
    (htransition : ∀ a q children,
      N.transition (symbolMap a) (stateEquiv q)
          (fun i => stateEquiv (children (Fin.cast (rankMap a) i))) =
        M.transition a q children)
    (t : Tree A) (q : Q) :
    N.RunsTo (relabelTree symbolMap rankMap t) (stateEquiv q) ↔ M.RunsTo t q := by
  induction t generalizing q with
  | node a children ih =>
      constructor
      · rintro ⟨targetStates, hstep, hruns⟩
        let sourceStates : Fin (A.rank a) → Q :=
          fun i => stateEquiv.symm (targetStates (Fin.cast (rankMap a).symm i))
        refine ⟨sourceStates, ?_, ?_⟩
        · rw [← htransition a q sourceStates]
          convert hstep using 2
          funext i
          simp [sourceStates]
        · intro i
          apply (ih i (sourceStates i)).mp
          simpa [sourceStates] using hruns (Fin.cast (rankMap a).symm i)
      · rintro ⟨sourceStates, hstep, hruns⟩
        let targetStates : Fin (B.rank (symbolMap a)) → R :=
          fun i => stateEquiv (sourceStates (Fin.cast (rankMap a) i))
        refine ⟨targetStates, ?_, ?_⟩
        · simpa [targetStates, htransition] using hstep
        · intro i
          apply (ih (Fin.cast (rankMap a) i)
            (sourceStates (Fin.cast (rankMap a) i))).mpr
          exact hruns (Fin.cast (rankMap a) i)

theorem relabelTree_accepts_iff {A B : RankedAlphabet} {Q R : Type*}
    (symbolMap : A.Symbol → B.Symbol)
    (rankMap : ∀ a, B.rank (symbolMap a) = A.rank a)
    (stateEquiv : Q ≃ R) (M : Automaton A Q) (N : Automaton B R)
    (htransition : ∀ a q children,
      N.transition (symbolMap a) (stateEquiv q)
          (fun i => stateEquiv (children (Fin.cast (rankMap a) i))) =
        M.transition a q children)
    (haccept : ∀ q, N.accept (stateEquiv q) = M.accept q)
    (t : Tree A) :
    N.Accepts (relabelTree symbolMap rankMap t) ↔ M.Accepts t := by
  constructor
  · rintro ⟨r, hr, hrun⟩
    refine ⟨stateEquiv.symm r, ?_, ?_⟩
    · rw [← haccept (stateEquiv.symm r)]
      simpa
    · simpa using (relabelTree_runsTo_iff symbolMap rankMap stateEquiv
        M N htransition t (stateEquiv.symm r)).mp (by simpa using hrun)
  · rintro ⟨q, hq, hrun⟩
    exact ⟨stateEquiv q, by simpa [haccept],
      (relabelTree_runsTo_iff symbolMap rankMap stateEquiv M N
        htransition t q).mpr hrun⟩

theorem ofFn_cast_eq {α : Type*} {m n : Nat} (h : m = n) (f : Fin n → α) :
    List.ofFn (fun i : Fin m => f (Fin.cast h i)) = List.ofFn f := by
  subst n
  rfl

/-- Relabel a ranked tree along a rank-preserving map of numbered alphabets. -/
def mapTree (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a) :
    Tree source.toRankedAlphabet → Tree target.toRankedAlphabet
  | .node a children =>
      .node (symbolMap a) fun i =>
        mapTree source target symbolMap rankMap
          (children (Fin.cast (rankMap a) i))

theorem mapTree_eq_relabelTree (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a) (t : Tree source.toRankedAlphabet) :
    mapTree source target symbolMap rankMap t =
      relabelTree symbolMap rankMap t := by
  induction t with
  | node a children ih =>
      simp only [mapTree, relabelTree, Tree.node.injEq, true_and]
      apply heq_of_eq
      funext i
      exact ih (Fin.cast (rankMap a) i)

theorem project_runsTo_of (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a)
    (sourceOf : Nat → List Nat)
    (hforward : ∀ a, a.val ∈ sourceOf (symbolMap a).val)
    (M : AutomatonCode) (t : Tree source.toRankedAlphabet) (q : Fin M.1)
    (hrun : (M.toAutomaton source).RunsTo t q) :
    ((project target sourceOf M).toAutomaton target).RunsTo
      (mapTree source target symbolMap rankMap t) q := by
  induction t generalizing q with
  | node a children ih =>
      rcases hrun with ⟨states, hstep, hruns⟩
      let targetStates : Fin (target.toRankedAlphabet.rank (symbolMap a)) → Fin M.1 :=
        fun i => states (Fin.cast (rankMap a) i)
      refine ⟨targetStates, ?_, ?_⟩
      · change ((FiniteAutomatonEncoding.encode target M.1
          (fun b q children => (sourceOf b).any fun source => step M source q children)
          (accepting M)).toAutomaton target).transition _ _ _ = true
        rw [FiniteAutomatonEncoding.transition_encode]
        apply List.any_eq_true.mpr
        refine ⟨a.val, hforward a, ?_⟩
        rw [show List.ofFn (fun i => (targetStates i).val) =
            List.ofFn (fun i => (states i).val) from
          ofFn_cast_eq (rankMap a) (fun i => (states i).val)]
        rw [step_eq_transition source M a q states]
        exact hstep
      · intro i
        exact ih (Fin.cast (rankMap a) i) (targetStates i)
          (hruns (Fin.cast (rankMap a) i))

theorem project_accepts_of (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a)
    (sourceOf : Nat → List Nat)
    (hforward : ∀ a, a.val ∈ sourceOf (symbolMap a).val)
    (M : AutomatonCode) (t : Tree source.toRankedAlphabet)
    (haccept : (M.toAutomaton source).Accepts t) :
    ((project target sourceOf M).toAutomaton target).Accepts
      (mapTree source target symbolMap rankMap t) := by
  rcases haccept with ⟨q, hq, hrun⟩
  refine ⟨q, ?_, project_runsTo_of source target symbolMap rankMap sourceOf
    hforward M t q hrun⟩
  change ((FiniteAutomatonEncoding.encode target M.1
    (fun b q children => (sourceOf b).any fun source => step M source q children)
    (accepting M)).toAutomaton target).accept q = true
  rw [FiniteAutomatonEncoding.accept_encode]
  exact accepting_eq_accept source M q ▸ hq

/-- Completeness of a numeric fiber enumeration: every listed source symbol
is in range and maps to the target symbol under consideration. -/
def CompleteFibers (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (sourceOf : Nat → List Nat) : Prop :=
  ∀ b sourceNumber, sourceNumber ∈ sourceOf b.val →
    ∃ a : source.toRankedAlphabet.Symbol,
      a.val = sourceNumber ∧ symbolMap a = b

theorem exists_source_of_project_runsTo (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a)
    (sourceOf : Nat → List Nat)
    (hcomplete : CompleteFibers source target symbolMap sourceOf)
    (M : AutomatonCode) (t : Tree target.toRankedAlphabet) (q : Fin M.1)
    (hrun : ((project target sourceOf M).toAutomaton target).RunsTo t q) :
    ∃ sourceTree : Tree source.toRankedAlphabet,
      mapTree source target symbolMap rankMap sourceTree = t ∧
        (M.toAutomaton source).RunsTo sourceTree q := by
  induction t generalizing q with
  | node b children ih =>
      rcases hrun with ⟨states, hstep, hruns⟩
      change ((FiniteAutomatonEncoding.encode target M.1
        (fun b q children => (sourceOf b).any fun source => step M source q children)
        (accepting M)).toAutomaton target).transition _ _ _ = true at hstep
      rw [FiniteAutomatonEncoding.transition_encode] at hstep
      obtain ⟨sourceNumber, hmem, hsourceStep⟩ := List.any_eq_true.mp hstep
      obtain ⟨a, haNumber, haMap⟩ := hcomplete b sourceNumber hmem
      subst b
      have hrank := rankMap a
      let sourceStates : Fin (source.toRankedAlphabet.rank a) → Fin M.1 :=
        fun i => states (Fin.cast hrank.symm i)
      have hwitness : ∀ i, ∃ sourceChild : Tree source.toRankedAlphabet,
          mapTree source target symbolMap rankMap sourceChild =
            children (Fin.cast hrank.symm i) ∧
          (M.toAutomaton source).RunsTo sourceChild (sourceStates i) := by
        intro i
        exact ih (Fin.cast hrank.symm i) (sourceStates i)
          (hruns (Fin.cast hrank.symm i))
      choose sourceChildren hmaps hrunsSource using hwitness
      let sourceTree : Tree source.toRankedAlphabet := .node a sourceChildren
      refine ⟨sourceTree, ?_, ?_⟩
      · simp only [sourceTree, mapTree, Tree.node.injEq, true_and]
        apply heq_of_eq
        funext i
        simpa [sourceTree] using hmaps (Fin.cast hrank i)
      · refine ⟨sourceStates, ?_, hrunsSource⟩
        rw [← step_eq_transition source M a q sourceStates]
        subst sourceNumber
        rw [show List.ofFn (fun i => (sourceStates i).val) =
            List.ofFn (fun i => (states i).val) from
          ofFn_cast_eq hrank.symm (fun i => (states i).val)]
        exact hsourceStep

theorem project_accepts_iff (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a)
    (sourceOf : Nat → List Nat)
    (hforward : ∀ a, a.val ∈ sourceOf (symbolMap a).val)
    (hcomplete : CompleteFibers source target symbolMap sourceOf)
    (M : AutomatonCode) (t : Tree target.toRankedAlphabet) :
    ((project target sourceOf M).toAutomaton target).Accepts t ↔
      ∃ sourceTree : Tree source.toRankedAlphabet,
        mapTree source target symbolMap rankMap sourceTree = t ∧
          (M.toAutomaton source).Accepts sourceTree := by
  constructor
  · rintro ⟨q, hq, hrun⟩
    obtain ⟨sourceTree, hmap, hrunSource⟩ :=
      exists_source_of_project_runsTo source target symbolMap rankMap sourceOf
        hcomplete M t q hrun
    refine ⟨sourceTree, hmap, q, ?_, hrunSource⟩
    change ((FiniteAutomatonEncoding.encode target M.1
      (fun b q children => (sourceOf b).any fun source => step M source q children)
      (accepting M)).toAutomaton target).accept q = true at hq
    rw [FiniteAutomatonEncoding.accept_encode] at hq
    exact accepting_eq_accept source M q ▸ hq
  · rintro ⟨sourceTree, rfl, haccept⟩
    exact project_accepts_of source target symbolMap rankMap sourceOf hforward
      M sourceTree haccept

theorem pullback_runsTo_iff (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a)
    (M : AutomatonCode) (t : Tree source.toRankedAlphabet) (q : Fin M.1) :
    ((pullback source (fun a =>
      if h : a < source.length then (symbolMap ⟨a, h⟩).val else 0) M).toAutomaton
        source).RunsTo t q ↔
      (M.toAutomaton target).RunsTo
        (mapTree source target symbolMap rankMap t) q := by
  rw [mapTree_eq_relabelTree]
  symm
  apply relabelTree_runsTo_iff symbolMap rankMap (Equiv.refl _)
    ((pullback source (fun a =>
      if h : a < source.length then (symbolMap ⟨a, h⟩).val else 0) M).toAutomaton
        source) (M.toAutomaton target)
  intro a q children
  change (M.toAutomaton target).transition (symbolMap a) q _ =
    ((FiniteAutomatonEncoding.encode source M.1
      (fun a q children => step M
        (if h : a < source.length then (symbolMap ⟨a, h⟩).val else 0)
        q children) (accepting M)).toAutomaton source).transition a q children
  rw [FiniteAutomatonEncoding.transition_encode]
  rw [show (if h : a.val < source.length then
      (symbolMap ⟨a.val, h⟩).val else 0) = (symbolMap a).val by simp [a.isLt]]
  simp only [Equiv.refl_apply]
  rw [← step_eq_transition target M (symbolMap a) q
    (fun i => children (Fin.cast (rankMap a) i))]
  congr 1
  exact ofFn_cast_eq (rankMap a) (fun i => (children i).val)

theorem pullback_accepts_iff (source target : RankedAlphabetCode)
    (symbolMap : source.toRankedAlphabet.Symbol → target.toRankedAlphabet.Symbol)
    (rankMap : ∀ a, target.toRankedAlphabet.rank (symbolMap a) =
      source.toRankedAlphabet.rank a)
    (M : AutomatonCode) (t : Tree source.toRankedAlphabet) :
    ((pullback source (fun a =>
      if h : a < source.length then (symbolMap ⟨a, h⟩).val else 0) M).toAutomaton
        source).Accepts t ↔
      (M.toAutomaton target).Accepts
        (mapTree source target symbolMap rankMap t) := by
  constructor
  · rintro ⟨q, hq, hrun⟩
    refine ⟨q, ?_, (pullback_runsTo_iff source target symbolMap rankMap M t q).mp hrun⟩
    change ((FiniteAutomatonEncoding.encode source M.1
      (fun a q children => step M
        (if h : a < source.length then (symbolMap ⟨a, h⟩).val else 0)
        q children) (accepting M)).toAutomaton source).accept q = true at hq
    rw [FiniteAutomatonEncoding.accept_encode] at hq
    simpa [accepting_eq_accept] using hq
  · rintro ⟨q, hq, hrun⟩
    refine ⟨q, ?_, (pullback_runsTo_iff source target symbolMap rankMap M t q).mpr hrun⟩
    change ((FiniteAutomatonEncoding.encode source M.1
      (fun a q children => step M
        (if h : a < source.length then (symbolMap ⟨a, h⟩).val else 0)
        q children) (accepting M)).toAutomaton source).accept q = true
    rw [FiniteAutomatonEncoding.accept_encode]
    simpa [accepting_eq_accept] using hq

end Lax53Proofs.EncodedProjection
