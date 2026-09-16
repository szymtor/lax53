import Lax759944Proofs.Legacy.Compile

/-! Every finite IMP command admits a finite, input-independent RAM layout. -/

namespace Lax842588Proofs.ImpLayout

open Lax759944Proofs.Legacy.Imp Lax759944Proofs.Legacy.Compile

def Extends (L K : Layout) : Prop :=
  (∀ s ∈ L.scalars, s ∈ K.scalars) ∧
    (∀ a ∈ L.arrays, a ∈ K.arrays) ∧ L.temps ≤ K.temps

def join (L K : Layout) : Layout :=
  ⟨L.scalars ++ K.scalars, L.arrays ++ K.arrays, L.temps + K.temps + 1⟩

theorem join_left (L K : Layout) : Extends L (join L K) := by
  refine ⟨fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h, ?_⟩
  dsimp [join]
  omega

theorem join_right (L K : Layout) : Extends K (join L K) := by
  refine ⟨fun _ h => List.mem_append_right _ h, fun _ h => List.mem_append_right _ h, ?_⟩
  dsimp [join]
  omega

theorem expr_mono {L K : Layout} (h : Extends L K) (e : Expr) (d : Nat) :
    Expr.Ok L e d → Expr.Ok K e d := by
  induction e generalizing d with
  | lit n => exact fun _ => trivial
  | var x => exact fun hx => h.1 x hx
  | get a i ih =>
    exact fun hx => ⟨h.2.1 a hx.1, ih d hx.2.1, lt_of_lt_of_le hx.2.2 h.2.2⟩
  | bin op e f ihe ihf =>
    exact fun hx => ⟨ihf d hx.1, ihe (d + 1) hx.2.1, lt_of_lt_of_le hx.2.2 h.2.2⟩

theorem com_mono {L K : Layout} (h : Extends L K) (c : Com) :
    Com.Ok L c → Com.Ok K c := by
  induction c with
  | skip => exact fun _ => trivial
  | assign x e => exact fun hx => ⟨h.1 x hx.1, expr_mono h e 0 hx.2⟩
  | store a i e => exact fun hx => ⟨h.2.1 a hx.1,
      expr_mono h i 0 hx.2.1, expr_mono h e 1 hx.2.2.1,
      lt_of_lt_of_le hx.2.2.2 h.2.2⟩
  | seq c d ihc ihd => exact fun hx => ⟨ihc hx.1, ihd hx.2⟩
  | ite b c d ihc ihd => exact fun hx =>
      ⟨expr_mono h (condExpr b) 0 hx.1, ihc hx.2.1, ihd hx.2.2⟩
  | «while» b c ih => exact fun hx => ⟨expr_mono h (condExpr b) 0 hx.1, ih hx.2⟩
  | read x => exact fun hx => h.1 x hx
  | write e => exact fun hx => ⟨expr_mono h e 0 hx.1, lt_of_lt_of_le hx.2 h.2.2⟩

theorem exists_expr (e : Expr) (d : Nat) : ∃ L : Layout, Expr.Ok L e d ∧ d < L.temps := by
  induction e generalizing d with
  | lit n => exact ⟨⟨[], [], d + 1⟩, trivial, by simp⟩
  | var x => exact ⟨⟨[x], [], d + 1⟩, by simp [Expr.Ok], by simp⟩
  | get a i ih =>
    obtain ⟨L, hi, hd⟩ := ih d
    let K : Layout := ⟨[], [a], 1⟩
    have hdepth : d < (join L K).temps := lt_of_lt_of_le hd (join_left L K).2.2
    exact ⟨join L K, ⟨by simp [join, K], expr_mono (join_left L K) i d hi, hdepth⟩, hdepth⟩
  | bin op e f ihe ihf =>
    obtain ⟨L, he, _⟩ := ihe (d + 1)
    obtain ⟨K, hf, hd⟩ := ihf d
    have hdepth : d < (join L K).temps := lt_of_lt_of_le hd (join_right L K).2.2
    exact ⟨join L K, ⟨expr_mono (join_right L K) f d hf,
      expr_mono (join_left L K) e (d + 1) he, hdepth⟩, hdepth⟩

theorem exists_layout (c : Com) : ∃ L : Layout, Com.Ok L c := by
  induction c with
  | skip => exact ⟨⟨[], [], 1⟩, trivial⟩
  | assign x e =>
    obtain ⟨L, he, _⟩ := exists_expr e 0
    let K : Layout := ⟨[x], [], 1⟩
    exact ⟨join L K, by simp [join, K], expr_mono (join_left L K) e 0 he⟩
  | store a i e =>
    obtain ⟨L, hi, hd⟩ := exists_expr i 0
    obtain ⟨K, he, _⟩ := exists_expr e 1
    let A : Layout := ⟨[], [a], 1⟩
    exact ⟨join L (join K A), by simp [join, A],
      expr_mono (join_left L (join K A)) i 0 hi,
      expr_mono (join_right L (join K A)) e 1 (expr_mono (join_left K A) e 1 he),
      lt_of_lt_of_le hd (join_left L (join K A)).2.2⟩
  | seq c d ihc ihd =>
    obtain ⟨L, hc⟩ := ihc
    obtain ⟨K, hd⟩ := ihd
    exact ⟨join L K, com_mono (join_left L K) c hc, com_mono (join_right L K) d hd⟩
  | ite b c d ihc ihd =>
    obtain ⟨L, hb, _⟩ := exists_expr (condExpr b) 0
    obtain ⟨K, hc⟩ := ihc
    obtain ⟨A, hd⟩ := ihd
    exact ⟨join L (join K A), expr_mono (join_left L (join K A)) (condExpr b) 0 hb,
      com_mono (join_right L (join K A)) c (com_mono (join_left K A) c hc),
      com_mono (join_right L (join K A)) d (com_mono (join_right K A) d hd)⟩
  | «while» b c ih =>
    obtain ⟨L, hb, _⟩ := exists_expr (condExpr b) 0
    obtain ⟨K, hc⟩ := ih
    exact ⟨join L K, expr_mono (join_left L K) (condExpr b) 0 hb,
      com_mono (join_right L K) c hc⟩
  | read x => exact ⟨⟨[x], [], 1⟩, by simp [Com.Ok]⟩
  | write e =>
    obtain ⟨L, he, hd⟩ := exists_expr e 0
    exact ⟨L, he, hd⟩

end Lax842588Proofs.ImpLayout
