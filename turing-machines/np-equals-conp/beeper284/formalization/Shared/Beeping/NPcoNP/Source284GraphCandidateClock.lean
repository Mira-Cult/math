import Shared.Beeping.NPcoNP.Source284GraphCandidateClockLoops

/-! Exact finite silent graph execution for the source candidate clock. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateClock
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphCandidateClockRows
open Shared.Beeping.NPcoNP.Source284GraphCandidateClockLoops
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- Exact graph cost of the remaining repeated multiplications. -/
def powCost (n p : Nat) : Nat → Nat
  | 0 => 1
  | j+1 => 2+multiplyCost n p+powCost n (p*(n+1)) j

/-- Compute a fixed power while storing the consumed exponent in register 11. -/
theorem pow_loop (b : Bank) (j n p z : Nat) :
    Seg ⟨91,bank b j n p 0 0 z⟩
      ⟨102,bank b 0 n (p*(n+1)^j) 0 0 (z+j)⟩ (powCost n p j) := by
  induction j generalizing p z with
  | zero => simp [powCost,Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row91_zero]
  | succ j ih =>
    have h₁ : Seg ⟨91,bank b (j+1) n p 0 0 z⟩ ⟨93,bank b j n p 0 0 (z+1)⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row91_pos,row92]
    have h₂ := multiply b j n p (z+1)
    have h₃ := ih (p*(n+1)) (z+1)
    have h := cat (cat h₁ h₂) h₃
    have hz : (z+1)+j=z+(j+1) := by omega
    have hp : (p*(n+1))*(n+1)^j=p*(n+1)^(j+1) := by rw [pow_succ]; ring
    simp only [powCost]
    simpa only [hz,hp] using h

/-- Restore the candidate index from the stored exponent. -/
theorem restore_index (b : Bank) (j n p a w z : Nat) :
    Seg ⟨102,bank b j n p a w z⟩ ⟨104,bank b (j+z) n p a w 0⟩ (2*z+1) := by
  induction z generalizing j with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row102_zero]
  | succ z ih =>
    have hs : Seg ⟨102,bank b j n p a w (z+1)⟩ ⟨102,bank b (j+1) n p a w z⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row102_pos,row103]
    have ht : 2*(z+1)+1=2+(2*z+1) := by omega
    have hj : j+1+z=j+(z+1) := by omega
    rw [ht,← hj]
    exact cat hs (ih (j+1))

def clockCost (j n old : Nat) : Nat := old+2+powCost n 1 j+(2*j+1)

/-- The candidate clock `(n+1)^j` is physically computed by the checked
graph in a strictly positive finite silent segment. The candidate index,
length, and all unaffected registers are preserved. -/
theorem clock (b : Bank) (j n old : Nat) :
    0 < clockCost j n old ∧
    Seg ⟨89,bank b j n old 0 0 0⟩ ⟨104,bank b j n ((n+1)^j) 0 0 0⟩
      (clockCost j n old) := by
  have h₁ := initialize_accumulator b j n old 0 0 0
  have h₂ := pow_loop b j n 1 0
  have h₃ := restore_index b 0 n ((n+1)^j) 0 0 j
  have h := cat (cat h₁ (by simpa using h₂)) (by simpa using h₃)
  refine ⟨by simp [clockCost], ?_⟩
  simpa [clockCost] using h

end Shared.Beeping.NPcoNP.Source284GraphCandidateClock
