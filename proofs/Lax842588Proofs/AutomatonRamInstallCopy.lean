import Lax842588Proofs.AutomatonRamInstall

namespace Lax842588Proofs.AutomatonRamCorrectness

set_option maxHeartbeats 1000000
open Classical

open Lax759944Proofs.Legacy.Imp
open Lax759944Proofs.Legacy.Reasoning
open Lax842588Proofs.ArrayInput
open Lax842588Proofs.AutomatonRamProgram

/-- Functional model of copying the first `upto` values into one flat row. -/
def writePrefix (array : List Nat) (base : Nat) (values : List Nat) : Nat → List Nat
  | 0 => array
  | upto + 1 =>
      (writePrefix array base values upto).set (base + upto) (values.getD upto 0)

@[simp] theorem writePrefix_zero (array : List Nat) (base : Nat) (values : List Nat) :
    writePrefix array base values 0 = array := rfl

theorem writePrefix_succ (array : List Nat) (base : Nat) (values : List Nat)
    (upto : Nat) :
    writePrefix array base values (upto + 1) =
      (writePrefix array base values upto).set (base + upto) (values.getD upto 0) := rfl

theorem writePrefix_length (array : List Nat) (base : Nat) (values : List Nat)
    (upto : Nat) :
    (writePrefix array base values upto).length = array.length := by
  induction upto with
  | zero => rfl
  | succ upto ih => simp [writePrefix, ih]

def CopyRowInv (states outputArray output : List Nat) (width target : Nat)
    (σ : Env) : Prop :=
  σ.arrs "O" = outputArray ∧
    σ.arrs "S" = writePrefix states (target * width) output (σ.vars "z") ∧
    σ.vars "T" = width ∧ σ.vars "target" = target ∧
    σ.vars "scratchLen" = output.length ∧ σ.vars "z" ≤ output.length

theorem installParentBody_spec (B : Nat)
    (states outputArray output : List Nat) (width target : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (houtputB : ∀ v ∈ output, v < B)
    (houtputArrayLenB : outputArray.length < B)
    (hprefix : PrefixEq outputArray output)
    (hwidthB : width < B) (htargetB : target < B)
    (houtputLenB : output.length < B)
    (hspan : target * width + output.length ≤ states.length)
    (hstatesLenB : states.length < B) :
    Spec B
      (fun σ => CopyRowInv states outputArray output width target σ ∧
        σ.vars "z" < output.length)
      installParentBody
      (fun σ σ' => CopyRowInv states outputArray output width target σ' ∧
        σ'.vars "z" = σ.vars "z" + 1)
      30 := by
  intro σ hσ
  have hz : σ.vars "z" < output.length := hσ.2
  have hzArray : σ.vars "z" < outputArray.length :=
    lt_of_lt_of_le hz hprefix.1
  have hO : outputArray.getD (σ.vars "z") 0 = output.getD (σ.vars "z") 0 :=
    hprefix.2 _ hz
  have hvalueB : outputArray.getD (σ.vars "z") 0 < B :=
    hO.trans_lt (getD_lt_of_mem_bound h0 houtputB)
  have haddr : target * width + σ.vars "z" < states.length := by omega
  have hcurrentLen :
      (writePrefix states (target * width) output (σ.vars "z")).length = states.length :=
    writePrefix_length states (target * width) output _
  have hcurrentAddr :
      target * width + σ.vars "z" <
        (writePrefix states (target * width) output (σ.vars "z")).length := by
    rw [hcurrentLen]
    exact haddr
  unfold installParentBody seqs
  run_vcg
  all_goals simp_all [CopyRowInv, writePrefix_succ]
  all_goals try exact hzArray
  all_goals omega

theorem installParentLoop_spec (B : Nat)
    (states outputArray output : List Nat) (width target : Nat)
    (hbody : Spec B
      (fun σ => CopyRowInv states outputArray output width target σ ∧
        σ.vars "z" < output.length)
      installParentBody
      (fun σ σ' => CopyRowInv states outputArray output width target σ' ∧
        σ'.vars "z" = σ.vars "z" + 1)
      30)
    (houtputLenB : output.length < B) :
    Spec B (CopyRowInv states outputArray output width target)
      installParentLoop
      (fun _ σ' => CopyRowInv states outputArray output width target σ' ∧
        σ'.vars "z" = output.length)
      (34 * output.length + 4) := by
  unfold installParentLoop
  exact Spec.forRange "z" "scratchLen"
    (CopyRowInv states outputArray output width target) output.length 30
    (34 * output.length + 4)
    (by rintro σ ⟨_, _, _, _, _, hz⟩; omega)
    (by rintro σ ⟨_, _, _, _, hlen, _⟩; omega)
    (by rintro _ ⟨_, _, _, _, hlen, _⟩; exact hlen)
    (by rintro _ ⟨_, _, _, _, _, hz⟩; exact hz)
    hbody (fun _ h => h)
    (fun _ _ => Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)

theorem installParent_spec (B : Nat)
    (states lengths outputArray output : List Nat) (width depth k : Nat)
    (h0 : 0 < B) (h1 : 1 < B)
    (houtputB : ∀ v ∈ output, v < B)
    (hprefix : PrefixEq outputArray output)
    (houtputArrayLenB : outputArray.length < B)
    (hstatesLenB : states.length < B) (hlengthsLenB : lengths.length < B)
    (hwidthB : width < B) (hdepthB : depth < B) (hkB : k < B)
    (hkdepth : k ≤ depth) (htarget : depth - k < lengths.length)
    (houtputLenB : output.length < B)
    (hspan : (depth - k) * width + output.length ≤ states.length) :
    Spec B
      (fun σ => σ.arrs "S" = states ∧ σ.arrs "L" = lengths ∧
        σ.arrs "O" = outputArray ∧ σ.vars "T" = width ∧
        σ.vars "depth" = depth ∧ σ.vars "k" = k ∧
        σ.vars "scratchLen" = output.length)
      installParent
      (fun _ σ' =>
        σ'.arrs "S" = writePrefix states ((depth - k) * width) output output.length ∧
        σ'.arrs "L" = lengths.set (depth - k) output.length ∧
        σ'.vars "depth" = depth - k + 1)
      (34 * output.length + 30) := by
  let target := depth - k
  have htargetB : target < B := by dsimp [target]; omega
  have hbody := installParentBody_spec B states outputArray output width target h0 h1
    houtputB houtputArrayLenB hprefix hwidthB htargetB houtputLenB hspan
    hstatesLenB
  have hloop0 := installParentLoop_spec B states outputArray output width target hbody
    houtputLenB
  have hloop : Spec B
      (fun τ => CopyRowInv states outputArray output width target τ ∧
        τ.arrs "L" = lengths)
      installParentLoop
      (fun _ τ' => (CopyRowInv states outputArray output width target τ' ∧
          τ'.vars "z" = output.length) ∧ τ'.arrs "L" = lengths)
      (34 * output.length + 4) :=
    (hloop0.pre (by rintro _ h; exact h.1)).frame.post (by
      rintro τ τ' hpre ⟨hq, _, harrs, _⟩
      exact ⟨hq, (harrs "L" (by decide)).trans hpre.2⟩)
  unfold installParent seqs
  run_vcg [hloop]
  all_goals simp_all [CopyRowInv, target, writePrefix_length]
  all_goals omega

end Lax842588Proofs.AutomatonRamCorrectness
