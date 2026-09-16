import Lax759944Proofs.LegacyRamBridge
import Mathlib.Tactic.Linarith

/-!
The existing IMP compiler targets the sequential machine retained privately
by the RAM/Turing submission. The checked instruction embedding below turns
that implementation into a program for the public `Lax808846` RAM, preserving
the supplied input and output lists. The target machine charges its terminal
instruction; one additional instruction suffices for this difference.
-/

namespace Lax842588Proofs.CheckedRamAdapter

open Lax759944Proofs.LegacyRamBridge

/-- Transfer a legacy implementation to the public RAM with an explicit
allowance for its terminal instruction. -/
theorem computesInTime {w : Nat} {p : Lax759944Proofs.Legacy.Ram.Program}
    {D : Set (List Nat)} {f : List Nat → List Nat} {T U : List Nat → Nat}
    (h : Lax759944Proofs.Legacy.RamComputes.ComputesInTime w p D f T)
    (hU : ∀ x ∈ D, T x + 1 ≤ U x) :
    Lax808846.RamComputes.ComputesInTime w (embedProgram p) D f U := by
  intro x hx
  obtain ⟨t, ht, hrun⟩ := Lax759944Proofs.LegacyRamBridge.computesInTime h x hx
  exact ⟨t, ht.trans (hU x hx), hrun⟩

/-- Increasing a positive-factor time coefficient by one covers the
additional terminal instruction. -/
theorem add_one_le_scaled (c n : Nat) (hn : 0 < n) :
    c * n + 1 ≤ (c + 1) * n := by
  nlinarith

end Lax842588Proofs.CheckedRamAdapter
