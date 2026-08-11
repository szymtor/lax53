import Lax53.TreeStructure

namespace Lax53Proofs.MSOSemantics

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Structure
open Lax52.MSOSyntax
open Lax52.MSOSemantics

universe u v w w'

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

@[simp] theorem realize_falsum {n m : Nat} {x : Fin n → M} {V : Fin m → Set M} :
    Realize (Formula.falsum : Formula L n m) x V ↔ False := Iff.rfl

@[simp] theorem realize_or {n m : Nat} {phi psi : Formula L n m}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (.or phi psi) x V ↔ Realize phi x V ∨ Realize psi x V := Iff.rfl

@[simp] theorem realize_neg {n m : Nat} {phi : Formula L n m}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (.neg phi) x V ↔ ¬Realize phi x V := Iff.rfl

@[simp] theorem realize_exFO {n m : Nat} {phi : Formula L (n + 1) m}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (.exFO phi) x V ↔ ∃ y : M, Realize phi (consVal y x) V := Iff.rfl

@[simp] theorem realize_exSO {n m : Nat} {phi : Formula L n (m + 1)}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (.exSO phi) x V ↔ ∃ X : Set M, Realize phi x (consVal X V) := Iff.rfl

@[simp] theorem realize_and {n m : Nat} {phi psi : Formula L n m}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (Formula.and phi psi) x V ↔ Realize phi x V ∧ Realize psi x V := by
  simp [Formula.and, Realize]

@[simp] theorem realize_verum {n m : Nat} {x : Fin n → M} {V : Fin m → Set M} :
    Realize (Formula.verum : Formula L n m) x V ↔ True := by
  simp [Formula.verum, Realize]

@[simp] theorem realize_imp {n m : Nat} {phi psi : Formula L n m}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.imp phi psi) x V ↔
      (Realize phi x V → Realize psi x V) := by
  simp only [Lax52.MSOSyntax.Formula.imp, Realize]
  tauto

@[simp] theorem realize_allFO {n m : Nat} {phi : Formula L (n + 1) m}
    {x : Fin n → M} {V : Fin m → Set M} :
    Realize (Lax52.MSOSyntax.Formula.allFO phi) x V ↔
      ∀ y : M, Realize phi (consVal y x) V := by
  simp [Lax52.MSOSyntax.Formula.allFO, Realize]

/-- MSO satisfaction is invariant under an isomorphism of first-order
structures, with monadic valuations transported by direct image. -/
theorem realize_equiv {N : Type w'} [L.Structure N] (e : M ≃[L] N) :
    {n m : Nat} → (phi : Formula L n m) →
      (v : Fin n → M) → (V : Fin m → Set M) →
      Realize phi (e ∘ v) (fun X => e '' V X) ↔ Realize phi v V
  | _, _, .falsum, _, _ => Iff.rfl
  | _, _, .equal t₁ t₂, v, _ => by
      simp only [Realize, HomClass.realize_term]
      exact e.injective.eq_iff
  | _, _, .rel r ts, v, _ => by
      simp only [Realize, HomClass.realize_term]
      exact StrongHomClass.map_rel e r (fun i => (ts i).realize v)
  | _, _, .mem t X, v, V => by
      simp only [Realize, HomClass.realize_term]
      constructor
      · rintro ⟨x, hx, he⟩
        exact e.injective he ▸ hx
      · intro hx
        exact ⟨t.realize v, hx, rfl⟩
  | _, _, .or phi psi, v, V => by
      simp only [Realize]
      rw [realize_equiv e phi v V, realize_equiv e psi v V]
  | _, _, .neg phi, v, V => by
      simp only [Realize]
      rw [realize_equiv e phi v V]
  | _, _, .exFO phi, v, V => by
      simp only [Realize]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨e.symm y, ?_⟩
        have hv : consVal y (e ∘ v) = e ∘ consVal (e.symm y) v := by
          funext i
          refine Fin.cases ?_ (fun _ => rfl) i
          simp [consVal]
        rw [hv] at hy
        exact (realize_equiv e phi _ V).mp hy
      · rintro ⟨x, hx⟩
        refine ⟨e x, ?_⟩
        have hv : consVal (e x) (e ∘ v) = e ∘ consVal x v := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rw [hv]
        exact (realize_equiv e phi _ V).mpr hx
  | _, _, .exSO phi, v, V => by
      simp only [Realize]
      constructor
      · rintro ⟨Y, hY⟩
        let X : Set M := e ⁻¹' Y
        refine ⟨X, ?_⟩
        have hsets : consVal Y (fun Z => e '' V Z) =
            fun Z => e '' consVal X V Z := by
          funext i
          refine Fin.cases ?_ (fun _ => rfl) i
          ext y
          change y ∈ Y ↔ y ∈ e '' X
          constructor
          · intro hy
            refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
            simpa [X] using hy
          · rintro ⟨x, hx, rfl⟩
            simpa [X] using hx
        rw [hsets] at hY
        exact (realize_equiv e phi v _).mp hY
      · rintro ⟨X, hX⟩
        refine ⟨e '' X, ?_⟩
        have hsets : consVal (e '' X) (fun Z => e '' V Z) =
            fun Z => e '' consVal X V Z := by
          funext i
          exact Fin.cases rfl (fun _ => rfl) i
        rw [hsets]
        exact (realize_equiv e phi v _).mpr hX

end Lax53Proofs.MSOSemantics
