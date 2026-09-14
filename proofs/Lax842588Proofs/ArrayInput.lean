import Lax865980Proofs.Lib.Fill

/-!
Array input for the Lax865980 IMP+ backend.

Adapted from the list-entry and array-prelude sections of
`Lax62Proofs.Refine.Codegen.Harness`, lax-archive/lax-submissions commit
`3639289680141e252c0cfc3c3f29071815391ffd` (Apache-2.0).
Only the reader and its supporting lemmas are retained, in this package's
namespace. Their definitions, specifications, and proofs are unchanged.
This keeps Lax842588's Lax865980 RAM model independent of Lax62's migration to Lax67.
-/

namespace Lax842588Proofs.ArrayInput

open Lax865980Proofs.Imp Lax865980Proofs.Reasoning Lax865980Proofs.Reasoning.Lib

/-- An entry of a list, as the `getD` that `arrOf` produces. -/
theorem getD_eq_getElem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 = l[i] :=
  (List.getElem_eq_getD 0).symm

/-- A list is the array of its own entries. -/
theorem arrOf_getD (l : List ℕ) : arrOf l.length (fun j => l.getD j 0) = l := by
  refine List.ext_getElem (by simp) (fun i h₁ h₂ => ?_)
  simp [arrOf, List.getElem?_eq_getElem h₂]

/-- Read as many further entries into the array `a` as the cell `m`
holds, in order: `x` is the counter, and each entry passes through `tmp`
on its way into the array. The array is *not* created — it already has
the length `ext` declared. -/
def readArr (a x m tmp : String) : Com :=
  .seq (.assign x (.lit 0))
    (.while (.lt (.var x) (.var m)) (.seq (.read tmp) (Fill.put a x (.var tmp))))

@[simp] theorem wvars_readArr (a x m tmp : String) :
    (readArr a x m tmp).wvars = [x, tmp, x] := by
  simp [readArr, Com.wvars]

@[simp] theorem warrs_readArr (a x m tmp : String) : (readArr a x m tmp).warrs = [a] := by
  simp [readArr, Com.warrs]

@[simp] theorem noWrite_readArr (a x m tmp : String) : (readArr a x m tmp).NoWrite := by
  simp [readArr, Com.NoWrite]

/-- **The array prelude.** The array has the right length already and
the cell `m` holds it; what comes back is the array holding exactly the
entries that were on the tape, the tape advanced past them, and the
counter at the end.

A turn costs `8` — the `read`'s `1` and `Fill.put`'s `7` — so the phase
costs `12·n + 6`. The four names have to be distinct in the three ways
the proof uses them: neither the counter nor the temporary may be the
length cell, and the `read` must not land on the counter. -/
theorem readArr_spec (B : ℕ) (a x m tmp : String) (ys rest : List ℕ)
    (hxm : x ≠ m) (htm : tmp ≠ m) (htx : tmp ≠ x)
    (hnB : ys.length < B) (hyB : ∀ v ∈ ys, v < B) :
    Spec B (fun σ => (σ.arrs a).length = ys.length ∧ σ.vars m = ys.length ∧
        σ.inp = ys ++ rest)
      (readArr a x m tmp)
      (fun _ σ' => σ'.arrs a = ys ∧ σ'.inp = rest ∧ σ'.vars x = ys.length)
      (12 * ys.length + 6) := by
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, ∀ j, F j = ys.getD j 0 := ⟨_, fun _ => rfl⟩
  have hFe : ∀ j, (h : j < ys.length) → F j = ys[j] := fun j h => by
    rw [hF]; exact getD_eq_getElem h
  have hFB : ∀ j, j < ys.length → F j < B := fun j h => by
    rw [hFe j h]; exact hyB _ (List.getElem_mem h)
  have hFarr : arrOf ys.length F = ys := by
    rw [show F = fun j => ys.getD j 0 from funext hF]; exact arrOf_getD ys
  have hbody : Spec B
      (fun τ => (Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧
        τ.inp = ys.drop (τ.vars x) ++ rest) ∧ τ.vars x < ys.length)
      (.seq (.read tmp) (Fill.put a x (.var tmp)))
      (fun τ τ' => (Fill.Below a x ys.length F τ' ∧ τ'.vars m = ys.length ∧
        τ'.inp = ys.drop (τ'.vars x) ++ rest) ∧ τ'.vars x = τ.vars x + 1) 8 := by
    refine (Spec.seq
      (Spec.read (x := tmp) (v := fun τ => F (τ.vars x))
        (rest := fun τ => ys.drop (τ.vars x + 1) ++ rest) ?_)
      ((Fill.put_spec B ys.length a x (.var tmp) F
        (fun τ => Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧ τ.vars x < ys.length ∧
          τ.vars tmp = F (τ.vars x) ∧ τ.inp = ys.drop (τ.vars x + 1) ++ rest)
        (fun τ hτ => ⟨hτ.1, hτ.2.2.1⟩) hnB
        (fun τ hτ => by
          rw [← hτ.2.2.2.1]
          exact evalB_var (by rw [hτ.2.2.2.1]; exact hFB _ hτ.2.2.1))).frame)
      ?_ ?_).mono (by simp)
    · rintro τ ⟨⟨-, -, hinp⟩, hlt⟩
      show τ.inp = F (τ.vars x) :: (ys.drop (τ.vars x + 1) ++ rest)
      rw [hinp, List.drop_eq_getElem_cons hlt, hFe _ hlt, List.cons_append]
    · rintro τ τ' ⟨⟨hb, hm, -⟩, hlt⟩ rfl
      exact ⟨hb.of_eq (by simp) (by simp [Ne.symm htx]), by simpa [Ne.symm htm] using hm,
        by simpa [Ne.symm htx] using hlt, by simp [Ne.symm htx], by simp [Ne.symm htx]⟩
    · rintro τ τ' τ'' ⟨⟨-, hm, -⟩, hlt⟩ rfl ⟨⟨hb'', hxx⟩, hfv, -, hfi, -⟩
      simp only [vars_setVar, if_neg (Ne.symm htx)] at hxx
      refine ⟨⟨hb'', ?_, ?_⟩, hxx⟩
      · rw [hfv m (by simp [Ne.symm hxm])]
        simpa [Ne.symm htm] using hm
      · rw [hfi (by simp), hxx]
  refine (((Spec.forRangeZero x m
    (fun τ => Fill.Below a x ys.length F τ ∧ τ.vars m = ys.length ∧
      τ.inp = ys.drop (τ.vars x) ++ rest)
    ys.length 8 hnB (fun τ hτ => hτ.1.le) (fun τ hτ => hτ.2.1) hbody).pre ?_).post ?_).mono
      (by omega)
  · rintro σ ⟨hlen, hm, hinp⟩
    refine ⟨Fill.below_zero (g := fun j => (σ.arrs a).getD j 0) ?_ (by simp), ?_, ?_⟩
    · rw [arrs_setVar, ← hlen, arrOf_getD]
    · simpa [Ne.symm hxm] using hm
    · simp [hinp]
  · rintro σ σ' - ⟨⟨hb, -, hinp⟩, hxe⟩
    obtain ⟨g, harr, hg⟩ := hb.done hxe
    exact ⟨by rw [harr, arrOf_congr hg, hFarr], by rw [hinp, hxe]; simp, hxe⟩

end Lax842588Proofs.ArrayInput
