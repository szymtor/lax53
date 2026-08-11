import Lax53Proofs.MarkedTreeLifts
import Lax53Proofs.MarkerProjection

namespace Lax53Proofs.QuantifierProjectionSemantics

open FirstOrder
open FirstOrder.Language
open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax53.RankedTree
open Lax53.TreeStructure
open Lax53Proofs.MarkedTrees
open Lax53Proofs.MarkedTreeLifts
open Lax53Proofs.MarkedTreeProjectionSemantics

universe u

noncomputable def foWitnessMark {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (z : Node t) : Node t → Bool := by
  classical
  exact fun p => decide (p = z)

noncomputable def soWitnessMark {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (X : Set (Node t)) : Node t → Bool := by
  classical
  exact fun p => decide (p ∈ X)

@[simp] theorem foWitnessMark_eq_true {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (z p : Node t) :
    foWitnessMark z p = true ↔ p = z := by
  classical
  simp [foWitnessMark]

@[simp] theorem soWitnessMark_eq_true {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} (X : Set (Node t)) (p : Node t) :
    soWitnessMark X p = true ↔ p ∈ X := by
  classical
  simp [soWitnessMark]

/-- A valid encoding stays valid after its newest first-order track is
forgotten. -/
theorem dropFO_represents {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A (n + 1) m)}
    {v : Fin (n + 1) → Node t} {V : Fin m → Set (Node t)}
    (h : Represents t v V) :
    Represents (dropFOTree t)
      (fun x => dropFONode (v x.succ))
      (fun X => dropFONode '' V X) := by
  rcases h with ⟨hv, hV⟩
  constructor
  · intro p x
    let q : Node t := liftFONode p
    have hp : dropFONode q = p := by simp [q]
    rw [← hp, dropFONode_label]
    change q.label.2.1 x.succ = true ↔ dropFONode (v x.succ) = dropFONode q
    rw [hv q x.succ]
    exact (dropFONodeEquiv t).injective.eq_iff.symm
  · intro p X
    let q : Node t := liftFONode p
    have hp : dropFONode q = p := by simp [q]
    rw [← hp, dropFONode_label]
    change q.label.2.2 X = true ↔ dropFONode q ∈ dropFONode '' V X
    rw [hV q X]
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨r, hr, her⟩
      have : r = q := (dropFONodeEquiv t).injective her
      simpa [this] using hr

/-- A valid encoding stays valid after its newest monadic track is
forgotten. -/
theorem dropSO_represents {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n (m + 1))}
    {v : Fin n → Node t} {V : Fin (m + 1) → Set (Node t)}
    (h : Represents t v V) :
    Represents (dropSOTree t)
      (fun x => dropSONode (v x))
      (fun X => dropSONode '' V X.succ) := by
  rcases h with ⟨hv, hV⟩
  constructor
  · intro p x
    let q : Node t := liftSONode p
    have hp : dropSONode q = p := by simp [q]
    rw [← hp, dropSONode_label]
    change q.label.2.1 x = true ↔ dropSONode (v x) = dropSONode q
    rw [hv q x]
    exact (dropSONodeEquiv t).injective.eq_iff.symm
  · intro p X
    let q : Node t := liftSONode p
    have hp : dropSONode q = p := by simp [q]
    rw [← hp, dropSONode_label]
    change q.label.2.2 X.succ = true ↔ dropSONode q ∈ dropSONode '' V X.succ
    rw [hV q X.succ]
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨r, hr, her⟩
      have : r = q := (dropSONodeEquiv t).injective her
      simpa [this] using hr

/-- Add a valid newest first-order track selecting `z`. -/
theorem liftFO_represents {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {v : Fin n → Node t}
    {V : Fin m → Set (Node t)} (h : Represents t v V) (z : Node t) :
    let mark := foWitnessMark z
    Represents (liftFOTreeWith t mark)
      (fun x => liftFOTreeNodeFrom mark (consVal z v x))
      (fun X => liftFOTreeNodeTo mark ⁻¹' V X) := by
  classical
  dsimp only
  rcases h with ⟨hv, hV⟩
  constructor
  · intro p x
    rw [liftFOTreeNode_label]
    refine Fin.cases ?_ (fun y => ?_) x
    · change foWitnessMark z (liftFOTreeNodeTo (foWitnessMark z) p) = true ↔
        liftFOTreeNodeFrom (foWitnessMark z) z = p
      rw [foWitnessMark_eq_true]
      constructor
      · intro hp
        calc
          liftFOTreeNodeFrom (foWitnessMark z) z =
              liftFOTreeNodeFrom (foWitnessMark z)
                (liftFOTreeNodeTo (foWitnessMark z) p) :=
            congrArg (liftFOTreeNodeFrom (foWitnessMark z)) hp.symm
          _ = p := liftFOTreeNodeFrom_to (foWitnessMark z) p
      · intro hp
        have := congrArg (liftFOTreeNodeTo (foWitnessMark z)) hp
        simpa using this.symm
    · change (liftFOTreeNodeTo (foWitnessMark z) p).label.2.1 y = true ↔
        liftFOTreeNodeFrom (foWitnessMark z) (v y) = p
      rw [hv (liftFOTreeNodeTo (foWitnessMark z) p) y]
      constructor
      · intro hp
        apply (liftFOTreeNodeEquiv t (foWitnessMark z)).injective
        simp [hp]
      · intro hp
        have := congrArg (liftFOTreeNodeTo (foWitnessMark z)) hp
        simpa using this
  · intro p X
    rw [liftFOTreeNode_label]
    change (liftFOTreeNodeTo (foWitnessMark z) p).label.2.2 X = true ↔
      liftFOTreeNodeTo (foWitnessMark z) p ∈ V X
    exact hV _ _

/-- Add a valid newest monadic track selecting `X`. -/
theorem liftSO_represents {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)} {v : Fin n → Node t}
    {V : Fin m → Set (Node t)} (h : Represents t v V) (X : Set (Node t)) :
    let mark := soWitnessMark X
    Represents (liftSOTreeWith t mark)
      (fun x => liftSOTreeNodeFrom mark (v x))
      (fun Y => liftSOTreeNodeTo mark ⁻¹' consVal X V Y) := by
  classical
  dsimp only
  rcases h with ⟨hv, hV⟩
  constructor
  · intro p x
    rw [liftSOTreeNode_label]
    change (liftSOTreeNodeTo (soWitnessMark X) p).label.2.1 x = true ↔
      liftSOTreeNodeFrom (soWitnessMark X) (v x) = p
    rw [hv (liftSOTreeNodeTo (soWitnessMark X) p) x]
    constructor
    · intro hp
      apply (liftSOTreeNodeEquiv t (soWitnessMark X)).injective
      simp [hp]
    · intro hp
      have := congrArg (liftSOTreeNodeTo (soWitnessMark X)) hp
      simpa using this
  · intro p Y
    rw [liftSOTreeNode_label]
    refine Fin.cases ?_ (fun Z => ?_) Y
    · change soWitnessMark X (liftSOTreeNodeTo (soWitnessMark X) p) = true ↔
        liftSOTreeNodeTo (soWitnessMark X) p ∈ X
      exact soWitnessMark_eq_true X _
    · change (liftSOTreeNodeTo (soWitnessMark X) p).label.2.2 Z = true ↔
        liftSOTreeNodeTo (soWitnessMark X) p ∈ V Z
      exact hV _ _

/-- Existential first-order quantification is projection of the newest
first-order marker track. -/
theorem formulaLanguage_exFO {A : RankedAlphabet.{u}} {n m : Nat}
    (phi : Formula (treeSignature A) (n + 1) m) :
    formulaLanguage (.exFO phi) =
      {t | ∃ source, dropFOTree source = t ∧ source ∈ formulaLanguage phi} := by
  classical
  ext t
  constructor
  · rintro ⟨v, V, hrep, z, hphi⟩
    let mark := foWitnessMark z
    let source := liftFOTreeWith t mark
    let sourceV : Fin m → Set (Node source) :=
      fun X => liftFOTreeNodeTo mark ⁻¹' V X
    let sourcev : Fin (n + 1) → Node source :=
      fun x => liftFOTreeNodeFrom mark (consVal z v x)
    refine ⟨source, dropFOTree_liftFOTreeWith t mark, sourcev, sourceV, ?_, ?_⟩
    · exact liftFO_represents hrep z
    · letI : (treeSignature A).Structure (Node source) := markedStructure source
      letI : (treeSignature A).Structure (Node t) := markedStructure t
      let e := liftFOTreeStructureEquiv t mark
      have hvmap : e ∘ sourcev = consVal z v := by
        funext x
        change liftFOTreeNodeTo mark
          (liftFOTreeNodeFrom mark (consVal z v x)) = consVal z v x
        exact liftFOTreeNodeTo_from mark _
      have hVmap : (fun X => e '' sourceV X) = V := by
        funext X
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact hq
        · intro hp
          refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
          change liftFOTreeNodeTo mark
            ((liftFOTreeStructureEquiv t mark).symm p) ∈ V X
          have he : liftFOTreeNodeTo mark
              ((liftFOTreeStructureEquiv t mark).symm p) = p :=
            e.apply_symm_apply p
          rwa [he]
      apply (Lax53Proofs.MSOSemantics.realize_equiv e phi sourcev sourceV).mp
      simpa only [hvmap, hVmap] using hphi
  · rintro ⟨source, rfl, v, V, hrep, hphi⟩
    letI : (treeSignature A).Structure (Node source) := markedStructure source
    letI : (treeSignature A).Structure (Node (dropFOTree source)) :=
      markedStructure (dropFOTree source)
    let e := dropFOStructureEquiv source
    let targetv : Fin n → Node (dropFOTree source) := fun x => e (v x.succ)
    let targetV : Fin m → Set (Node (dropFOTree source)) := fun X => e '' V X
    refine ⟨targetv, targetV, ?_, e (v 0), ?_⟩
    · exact dropFO_represents hrep
    · have hvmap : consVal (e (v 0)) targetv = e ∘ v := by
        funext x
        exact Fin.cases rfl (fun _ => rfl) x
      have ht := (Lax53Proofs.MSOSemantics.realize_equiv e phi v V).mpr hphi
      simpa only [hvmap, targetV] using ht

/-- Existential monadic quantification is projection of the newest monadic
marker track. -/
theorem formulaLanguage_exSO {A : RankedAlphabet.{u}} {n m : Nat}
    (phi : Formula (treeSignature A) n (m + 1)) :
    formulaLanguage (.exSO phi) =
      {t | ∃ source, dropSOTree source = t ∧ source ∈ formulaLanguage phi} := by
  classical
  ext t
  constructor
  · rintro ⟨v, V, hrep, X, hphi⟩
    let mark := soWitnessMark X
    let source := liftSOTreeWith t mark
    let sourcev : Fin n → Node source :=
      fun x => liftSOTreeNodeFrom mark (v x)
    let sourceV : Fin (m + 1) → Set (Node source) :=
      fun Y => liftSOTreeNodeTo mark ⁻¹' consVal X V Y
    refine ⟨source, dropSOTree_liftSOTreeWith t mark, sourcev, sourceV, ?_, ?_⟩
    · exact liftSO_represents hrep X
    · letI : (treeSignature A).Structure (Node source) := markedStructure source
      letI : (treeSignature A).Structure (Node t) := markedStructure t
      let e := liftSOTreeStructureEquiv t mark
      have hvmap : e ∘ sourcev = v := by
        funext x
        change liftSOTreeNodeTo mark (liftSOTreeNodeFrom mark (v x)) = v x
        exact liftSOTreeNodeTo_from mark _
      have hVmap : (fun Y => e '' sourceV Y) = consVal X V := by
        funext Y
        ext p
        constructor
        · rintro ⟨q, hq, rfl⟩
          exact hq
        · intro hp
          refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
          change liftSOTreeNodeTo mark
            ((liftSOTreeStructureEquiv t mark).symm p) ∈ consVal X V Y
          have he : liftSOTreeNodeTo mark
              ((liftSOTreeStructureEquiv t mark).symm p) = p :=
            e.apply_symm_apply p
          rwa [he]
      apply (Lax53Proofs.MSOSemantics.realize_equiv e phi sourcev sourceV).mp
      simpa only [hvmap, hVmap] using hphi
  · rintro ⟨source, rfl, v, V, hrep, hphi⟩
    letI : (treeSignature A).Structure (Node source) := markedStructure source
    letI : (treeSignature A).Structure (Node (dropSOTree source)) :=
      markedStructure (dropSOTree source)
    let e := dropSOStructureEquiv source
    let targetv : Fin n → Node (dropSOTree source) := fun x => e (v x)
    let targetV : Fin m → Set (Node (dropSOTree source)) := fun X => e '' V X.succ
    refine ⟨targetv, targetV, ?_, e '' V 0, ?_⟩
    · exact dropSO_represents hrep
    · have hVmap : consVal (e '' V 0) targetV = fun X => e '' V X := by
        funext X
        exact Fin.cases rfl (fun _ => rfl) X
      have ht := (Lax53Proofs.MSOSemantics.realize_equiv e phi v V).mpr hphi
      simpa only [targetv, hVmap] using ht

end Lax53Proofs.QuantifierProjectionSemantics
