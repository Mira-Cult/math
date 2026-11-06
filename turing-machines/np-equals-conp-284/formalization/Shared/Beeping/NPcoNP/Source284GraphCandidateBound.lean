import Shared.Beeping.NPcoNP.Source284GraphCandidateBoundRows

/-! Finite paid graph execution for the exhaustive candidate certificate
bound, including clock restoration. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateBound
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphCandidateBoundRows
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem initialize_bound (b : Bank) (p h w z : Nat) :
    Seg ⟨104,bank b p h w z⟩ ⟨106,bank b p 1 w z⟩ (h+2) := by
  induction h with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row104_zero,row105]
  | succ h ih =>
    have hs : Seg ⟨104,bank b p (h+1) w z⟩ ⟨104,bank b p h w z⟩ 1 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row104_pos]
    have ht : h+1+2=1+(h+2) := by omega
    rw [ht]
    exact cat hs ih

theorem double_drain (b : Bank) (p h w z : Nat) :
    Seg ⟨108,bank b p h w z⟩ ⟨111,bank b p 0 (w+2*h) z⟩ (3*h+1) := by
  induction h generalizing w with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row108_zero]
  | succ h ih =>
    have hs : Seg ⟨108,bank b p (h+1) w z⟩ ⟨108,bank b p h (w+2) z⟩ 3 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row108_pos,row109,row110]
    have hw : w+2+2*h=w+2*(h+1) := by omega
    have ht : 3*(h+1)+1=3+(3*h+1) := by omega
    rw [ht,← hw]
    exact cat hs (ih (w+2))

theorem double_restore (b : Bank) (p h w z : Nat) :
    Seg ⟨111,bank b p h w z⟩ ⟨106,bank b p (h+w) 0 z⟩ (2*w+1) := by
  induction w generalizing h with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row111_zero]
  | succ w ih =>
    have hs : Seg ⟨111,bank b p h (w+1) z⟩ ⟨111,bank b p (h+1) w z⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row111_pos,row112]
    have hh : h+1+w=h+(w+1) := by omega
    have ht : 2*(w+1)+1=2+(2*w+1) := by omega
    rw [ht,← hh]
    exact cat hs (ih (h+1))

theorem double_bound (b : Bank) (p h z : Nat) :
    Seg ⟨108,bank b p h 0 z⟩ ⟨106,bank b p (2*h) 0 z⟩ (7*h+2) := by
  have h₁ := double_drain b p h 0 z
  have h₂ := double_restore b p 0 (2*h) z
  have hs := cat h₁ (by simpa using h₂)
  have hc : (3*h+1)+(2*(2*h)+1)=7*h+2 := by omega
  simpa only [zero_add,hc] using hs

def powCost (h : Nat) : Nat → Nat
  | 0 => 1
  | p+1 => 2+(7*h+2)+powCost (2*h) p

/-- Build `h * 2^p` while saving the consumed clock in register 11. -/
theorem pow_loop (b : Bank) (p h z : Nat) :
    Seg ⟨106,bank b p h 0 z⟩ ⟨113,bank b 0 (h*2^p) 0 (z+p)⟩ (powCost h p) := by
  induction p generalizing h z with
  | zero => simp [powCost,Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row106_zero]
  | succ p ih =>
    have h₁ : Seg ⟨106,bank b (p+1) h 0 z⟩ ⟨108,bank b p h 0 (z+1)⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row106_pos,row107]
    have h₂ := double_bound b p h (z+1)
    have h₃ := ih (2*h) (z+1)
    have hseg := cat (cat h₁ h₂) h₃
    have hz : z+1+p=z+(p+1) := by omega
    have hh : (2*h)*2^p = h*2^(p+1) := by rw [pow_succ]; ring
    simp only [powCost]
    simpa only [hz,hh] using hseg

theorem restore_clock (b : Bank) (p h z : Nat) :
    Seg ⟨113,bank b p h 0 z⟩ ⟨115,bank b (p+z) h 0 0⟩ (2*z+1) := by
  induction z generalizing p with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row113_zero]
  | succ z ih =>
    have hs : Seg ⟨113,bank b p h 0 (z+1)⟩ ⟨113,bank b (p+1) h 0 z⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row113_pos,row114]
    have hp : p+1+z=p+(z+1) := by omega
    have ht : 2*(z+1)+1=2+(2*z+1) := by omega
    rw [ht,← hp]
    exact cat hs (ih (p+1))

def boundCost (clock old : Nat) : Nat := old+2+powCost 1 clock+(2*clock+1)

/-- The graph constructs exactly `2^clock` certificate attempts and restores
the clock. Its two arithmetic scratch registers are zero on exit. -/
theorem bound (b : Bank) (clock old : Nat) :
    0 < boundCost clock old ∧
    Seg ⟨104,bank b clock old 0 0⟩ ⟨115,bank b clock (2^clock) 0 0⟩
      (boundCost clock old) := by
  have h₁ := initialize_bound b clock old 0 0
  have h₂ := pow_loop b clock 1 0
  have h₃ := restore_clock b 0 (2^clock) clock
  have hs := cat (cat h₁ (by simpa using h₂)) (by simpa using h₃)
  refine ⟨by simp [boundCost],?_⟩
  simpa [boundCost] using hs

end Shared.Beeping.NPcoNP.Source284GraphCandidateBound
