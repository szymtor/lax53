import Lax842588Proofs.AutomatonRamArenaRead

/-!
Proof-only semantic interface shared by the three represented-list scans in
the structural frontend. Numerical tags remain confined to this operational
layer.
-/

namespace Lax842588Proofs.AutomatonRamArenaCorrectness

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588Proofs.ArrayInput
open Lax842588Proofs.ArenaSemantics
open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- The fixed IMP+ condition used to recognize a represented cons cell. -/
def representedListCondition (cursorVariable : String) : Cond :=
  .eq (.get "Arena" (.var cursorVariable)) (.lit WordImage.pairTag)

private theorem cursorLookup (I : WordImage) (address tag : Nat)
    (hvalid : I.ValidAddress address)
    (htag : (arenaWords I).getD address 0 = tag) :
    (arenaWords I)[address]? = some tag := by
  have hlt := Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalid
  rw [List.getElem?_eq_getElem (by omega)]
  rw [← Lax842588Proofs.ArrayInput.getD_eq_getElem (by omega)]
  exact congrArg some htag

theorem representedListCondition_value {alpha : Type} (B : Nat)
    (I : WordImage) (P : Presentation alpha) (xs : List alpha)
    (cursor : Nat) (cursorVariable : String) (sigma : Env)
    (h1 : 1 < B) (hmemB : I.memoryWords < B)
    (hloaded : ArenaLoaded I sigma)
    (hcursor : sigma.vars cursorVariable = cursor)
    (hrep : I.Represents cursor ((list P).toRaw xs)) :
    (representedListCondition cursorVariable).evalB B sigma =
      some (!xs.isEmpty) := by
  have hvalid := Lax842588Proofs.ArenaSemantics.Represents.valid hrep
  have hcursorLen :=
    Lax842588Proofs.ArenaSemantics.ValidAddress.lt_arenaWords_length hvalid
  have harenaLength : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hcursorB : cursor < B := by omega
  have hvar : (Expr.var cursorVariable).evalB B sigma = some cursor := by
    rw [evalB_var_iff]
    exact ⟨hcursor.symm, by simpa [hcursor] using hcursorB⟩
  have htag := Lax842588Proofs.ArenaSemantics.Represents.list_tag hrep
  cases xs with
  | nil =>
      have hlookup := cursorLookup I cursor WordImage.natTag hvalid (by
        simpa using htag)
      have hlookup' : (sigma.arrs "Arena")[cursor]? = some WordImage.natTag := by
        simpa [hloaded.1] using hlookup
      have hget := evalB_get hvar hlookup' (by simp [WordImage.natTag]; omega)
      simpa [representedListCondition, WordImage.natTag, WordImage.pairTag] using
        (evalB_condEq hget (evalB_lit h1))
  | cons x xs =>
      have hlookup := cursorLookup I cursor WordImage.pairTag hvalid (by
        simpa using htag)
      have hlookup' : (sigma.arrs "Arena")[cursor]? = some WordImage.pairTag := by
        simpa [hloaded.1] using hlookup
      have hget := evalB_get hvar hlookup' (by simpa [WordImage.pairTag] using h1)
      simpa [representedListCondition, WordImage.pairTag] using
        (evalB_condEq hget (evalB_lit h1))

end Lax842588Proofs.AutomatonRamArenaCorrectness
