import Lax842588Proofs.AutomatonRamArenaRead

/-!
Compositional reads of constructor fields in the certified arena. A fixed
binary path is compiled to nested word reads, with its actual expression
cost. Paths are proof-side descriptions of the existing constructor layout,
not input annotations or alternative encoders.
-/

namespace Lax842588Proofs.ArenaFieldAccess

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Reasoning
open Lax759944Proofs.Legacy.Compile
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.AutomatonRamArenaCorrectness
open Lax560851.StructuralPresentation Lax560851.WordArena

/-- `false` selects a pair's left field; `true` selects its right field. -/
def atPath : Raw → List Bool → Option Raw
  | raw, [] => some raw
  | .nat _, _ :: _ => none
  | .pair left _, false :: path => atPath left path
  | .pair _ right, true :: path => atPath right path

def follow (root : Expr) : List Bool → Expr
  | [] => root
  | right :: path =>
      follow (.get "Arena" (.add root (.lit (if right then 2 else 1)))) path

def payload (root : Expr) (path : List Bool) : Expr :=
  .get "Arena" (.add (follow root path) (.lit 1))

theorem readCell_eval (B : Nat) (I : WordImage) (σ : Env)
    (root : Expr) (address offset value : Nat)
    (hloaded : σ.arrs "Arena" = arenaWords I) (hmem : I.memoryWords < B)
    (haddress : I.ValidAddress address) (hoffset : offset ≤ 2)
    (hroot : root.evalB B σ = some address)
    (hword : (arenaWords I).getD (address + offset) 0 = value) (hvalue : value < B) :
    (Expr.get "Arena" (.add root (.lit offset))).evalB B σ = some value := by
  have hvalid := ValidAddress.lt_arenaWords_length haddress
  have hlen : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hi : address + offset < (arenaWords I).length := by omega
  have hget : (σ.arrs "Arena")[address + offset]? = some value := by
    rw [hloaded, List.getElem?_eq_getElem hi,
      ← List.getD_eq_getElem (l := arenaWords I) (d := 0) hi, hword]
  apply evalB_get (evalB_bin hroot (evalB_lit (show offset < B by omega))
    (show Bop.add.apply address offset < B by simp; omega)) hget hvalue

theorem follow_represents (B : Nat) (I : WordImage) (σ : Env)
    (hloaded : σ.arrs "Arena" = arenaWords I) (hmem : I.memoryWords < B)
    (path : List Bool) :
    ∀ (raw leaf : Raw) (address : Nat) (root : Expr),
      I.Represents address raw → root.evalB B σ = some address →
      atPath raw path = some leaf →
      ∃ target, (follow root path).evalB B σ = some target ∧ I.Represents target leaf := by
  induction path with
  | nil =>
      intro raw leaf address root hrep hroot hpath
      have he : raw = leaf := by simpa [atPath] using hpath
      exact ⟨address, hroot, he ▸ hrep⟩
  | cons right path ih =>
      intro raw leaf address root hrep hroot hpath
      cases raw with
      | nat n => simp [atPath] at hpath
      | pair leftRaw rightRaw =>
          obtain ⟨left, rightAddress, _, hleft, hright, hlrep, hrrep⟩ :=
            Represents.pair_words hrep
          have hvalid := Represents.valid hrep
          have hlvalid := ValidAddress.lt_arenaWords_length (Represents.valid hlrep)
          have hrvalid := ValidAddress.lt_arenaWords_length (Represents.valid hrrep)
          have hlen : (arenaWords I).length = I.memoryWords := by
            simp [arenaWords, WordImage.memoryWords]
          cases right with
          | false =>
              have hread := readCell_eval B I σ root address 1 left hloaded hmem
                hvalid (by omega) hroot hleft (by omega)
              exact ih leftRaw leaf left _ hlrep hread hpath
          | true =>
              have hread := readCell_eval B I σ root address 2 rightAddress hloaded hmem
                hvalid (by omega) hroot hright (by omega)
              exact ih rightRaw leaf rightAddress _ hrrep hread hpath

theorem payload_eval (B : Nat) (I : WordImage) (σ : Env)
    (hloaded : σ.arrs "Arena" = arenaWords I) (hmem : I.memoryWords < B)
    (raw : Raw) (path : List Bool) (address value : Nat) (root : Expr)
    (hrep : I.Represents address raw) (hroot : root.evalB B σ = some address)
    (hpath : atPath raw path = some (.nat value)) (hvalue : value < B) :
    (payload root path).evalB B σ = some value := by
  obtain ⟨target, hfollow, htarget⟩ :=
    follow_represents B I σ hloaded hmem path raw (.nat value) address root hrep hroot hpath
  exact readCell_eval B I σ (follow root path) target 1 value hloaded hmem
    (Represents.valid htarget) (by omega) hfollow
    (Represents.nat_words htarget).2.1 hvalue

theorem follow_size (root : Expr) (path : List Bool) :
    (follow root path).size = root.size + 3 * path.length := by
  induction path generalizing root with
  | nil => simp [follow]
  | cons right path ih => simp [follow, ih, Expr.size]; omega

theorem payload_size (root : Expr) (path : List Bool) :
    (payload root path).size = root.size + 3 * path.length + 3 := by
  simp [payload, Expr.size, follow_size]

/-- The charged assignment reads only the certified primitive payload at the
specified field path. All address arithmetic is included in the cost. -/
theorem load_spec (B : Nat) (I : WordImage) (raw : Raw) (path : List Bool)
    (address value : Nat) (src dst : String) (hmem : I.memoryWords < B)
    (hrep : I.Represents address raw) (hpath : atPath raw path = some (.nat value))
    (hvalue : value < B) :
    Spec B (fun σ => σ.arrs "Arena" = arenaWords I ∧ σ.vars src = address)
      (.assign dst (payload (.var src) path))
      (fun _ σ => σ.vars dst = value) (3 * path.length + 5) := by
  intro σ hσ
  have hvalid := ValidAddress.lt_arenaWords_length (Represents.valid hrep)
  have hlen : (arenaWords I).length = I.memoryWords := by
    simp [arenaWords, WordImage.memoryWords]
  have hroot : (Expr.var src).evalB B σ = some address := by
    simp [Expr.evalB, hσ.2, fit_self (show address < B by omega)]
  have hread := payload_eval B I σ hσ.1 hmem raw path address value (.var src)
    hrep hroot hpath hvalue
  refine ⟨σ.setVar dst value, (Run.assign hread).mono ?_, by simp⟩
  simp [payload_size, Expr.size]
  omega

theorem follow_ok (L : Layout) (path : List Bool) (root : Expr) (d : Nat)
    (hroot : Expr.Ok L root (d + path.length))
    (ha : "Arena" ∈ L.arrays) (ht : d + path.length < L.temps) :
    Expr.Ok L (follow root path) d := by
  induction path generalizing root d with
  | nil => simpa [follow] using hroot
  | cons right path ih =>
      apply ih
      · simpa [Expr.Ok, ha, Nat.add_assoc] using
          (show Expr.Ok L root (d + path.length + 1) ∧ d + path.length < L.temps from
            ⟨by simpa using! hroot, by simpa using Nat.lt_of_succ_lt ht⟩)
      · simpa using Nat.lt_of_succ_lt ht

theorem load_ok (L : Layout) (path : List Bool) (src dst : String)
    (hs : src ∈ L.scalars) (hd : dst ∈ L.scalars) (ha : "Arena" ∈ L.arrays)
    (ht : path.length + 2 ≤ L.temps) :
    Com.Ok L (.assign dst (payload (.var src) path)) := by
  have hf := follow_ok L path (.var src) 1 (by simpa [Expr.Ok] using hs) ha (by omega)
  simpa [Com.Ok, payload, Expr.Ok, hd, ha] using
    (show Expr.Ok L (follow (.var src) path) 1 ∧ 0 < L.temps from ⟨hf, by omega⟩)

end Lax842588Proofs.ArenaFieldAccess
