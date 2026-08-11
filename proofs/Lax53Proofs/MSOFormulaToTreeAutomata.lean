import Lax53Proofs.AtomicMarkedTrees
import Lax53Proofs.QuantifierProjectionSemantics

namespace Lax53Proofs.MSOFormulaToTreeAutomata

open Lax52.MSOSyntax
open Lax52.MSOSemantics
open Lax53.RankedTree
open Lax53.TreeAutomaton
open Lax53.TreeStructure
open Lax53Proofs.MarkedTrees
open Lax53Proofs.TreeAutomataClosure
open Lax53Proofs.AtomicMarkedTrees
open Lax53Proofs.MarkerProjection
open Lax53Proofs.QuantifierProjectionSemantics

universe u

theorem represents_unique {A : RankedAlphabet.{u}} {n m : Nat}
    {t : Tree (MarkedAlphabet A n m)}
    {v w : Fin n → Node t} {V W : Fin m → Set (Node t)}
    (hv : Represents t v V) (hw : Represents t w W) : v = w ∧ V = W := by
  rcases hv with ⟨hv, hV⟩
  rcases hw with ⟨hw, hW⟩
  constructor
  · funext x
    exact ((hw (v x) x).mp ((hv (v x) x).mpr rfl)).symm
  · funext X
    ext p
    exact (hV p X).symm.trans (hW p X)

theorem formulaLanguage_or {A : RankedAlphabet.{u}} {n m : Nat}
    (phi psi : Formula (treeSignature A) n m) :
    formulaLanguage (.or phi psi) = formulaLanguage phi ∪ formulaLanguage psi := by
  ext t
  constructor
  · rintro ⟨v, V, hrep, hphi | hpsi⟩
    · exact Or.inl ⟨v, V, hrep, hphi⟩
    · exact Or.inr ⟨v, V, hrep, hpsi⟩
  · rintro (⟨v, V, hrep, hphi⟩ | ⟨v, V, hrep, hpsi⟩)
    · exact ⟨v, V, hrep, Or.inl hphi⟩
    · exact ⟨v, V, hrep, Or.inr hpsi⟩

theorem formulaLanguage_neg {A : RankedAlphabet.{u}} {n m : Nat}
    (phi : Formula (treeSignature A) n m) :
    formulaLanguage (.neg phi) =
      validMarkedLanguage A n m ∩ {t | t ∉ formulaLanguage phi} := by
  ext t
  constructor
  · rintro ⟨v, V, hrep, hnot⟩
    refine ⟨⟨v, V, hrep⟩, ?_⟩
    rintro ⟨w, W, hrep', hphi⟩
    obtain ⟨rfl, rfl⟩ := represents_unique hrep hrep'
    exact hnot hphi
  · rintro ⟨⟨v, V, hrep⟩, hnotmem⟩
    refine ⟨v, V, hrep, ?_⟩
    intro hphi
    exact hnotmem ⟨v, V, hrep, hphi⟩

theorem formulaLanguage_recognizable {A : RankedAlphabet.{u}} :
    {n m : Nat} → (phi : Formula (treeSignature A) n m) →
      Recognizable (formulaLanguage phi)
  | _, _, .falsum => formulaLanguage_falsum_recognizable
  | _, _, .equal t₁ t₂ => formulaLanguage_equal_recognizable t₁ t₂
  | _, _, .rel r ts => by
      cases r with
      | label a => exact formulaLanguage_label_recognizable a ts
      | child slot => exact formulaLanguage_child_recognizable slot ts
  | _, _, .mem t X => formulaLanguage_mem_recognizable t X
  | _, _, .or phi psi => by
      rw [formulaLanguage_or]
      exact recognizable_union _ _
        (formulaLanguage_recognizable phi) (formulaLanguage_recognizable psi)
  | n, m, .neg phi => by
      rw [formulaLanguage_neg]
      exact recognizable_intersection _ _
        (Lax53Proofs.ValidMarkedTrees.validMarked_recognizable A n m)
        (recognizable_complement _ (formulaLanguage_recognizable phi))
  | _, _, .exFO phi => by
      rcases formulaLanguage_recognizable phi with ⟨Q, hQ, M, hM⟩
      letI := hQ
      refine ⟨Q, inferInstance, projectFO M, ?_⟩
      ext t
      change (projectFO M).Accepts t ↔ t ∈ formulaLanguage (.exFO phi)
      rw [projectFO_accepts_iff]
      rw [formulaLanguage_exFO]
      constructor <;> rintro ⟨source, hdrop, hsource⟩
      · have hs : source ∈ M.language := hsource
        rw [hM] at hs
        exact ⟨source, hdrop, hs⟩
      · have hs : source ∈ M.language := by
          rw [hM]
          exact hsource
        exact ⟨source, hdrop, hs⟩
  | _, _, .exSO phi => by
      rcases formulaLanguage_recognizable phi with ⟨Q, hQ, M, hM⟩
      letI := hQ
      refine ⟨Q, inferInstance, projectSO M, ?_⟩
      ext t
      change (projectSO M).Accepts t ↔ t ∈ formulaLanguage (.exSO phi)
      rw [projectSO_accepts_iff]
      rw [formulaLanguage_exSO]
      constructor <;> rintro ⟨source, hdrop, hsource⟩
      · have hs : source ∈ M.language := hsource
        rw [hM] at hs
        exact ⟨source, hdrop, hs⟩
      · have hs : source ∈ M.language := by
          rw [hM]
          exact hsource
        exact ⟨source, hdrop, hs⟩

end Lax53Proofs.MSOFormulaToTreeAutomata
