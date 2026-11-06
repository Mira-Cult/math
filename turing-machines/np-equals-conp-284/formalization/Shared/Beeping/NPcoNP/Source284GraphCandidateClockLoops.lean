import Shared.Beeping.NPcoNP.Source284GraphCandidateClockRows

/-! Terminating arithmetic loops for the candidate clock in the pinned
register graph. Every duration counts actual graph transitions. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateClockLoops
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphCandidateClockRows
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg cat)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- Clear the old description and initialize the power accumulator to one. -/
theorem initialize_accumulator (b : Bank) (j n p a w z : Nat) :
    Seg ⟨89,bank b j n p a w z⟩ ⟨91,bank b j n 1 a w z⟩ (p+2) := by
  induction p with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row89_zero,row90]
  | succ p ih =>
    have hs : Seg ⟨89,bank b j n (p+1) a w z⟩ ⟨89,bank b j n p a w z⟩ 1 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row89_pos]
    have ht : p+1+2 = 1+(p+2) := by omega
    rw [ht]
    exact cat hs ih

/-- Copy the length into both scratch accumulators while clearing its register. -/
theorem copy_length (b : Bank) (j n p a w z : Nat) :
    Seg ⟨94,bank b j n p a w z⟩ ⟨97,bank b j 0 p (a+n) (w+n) z⟩ (3*n+1) := by
  induction n generalizing a w with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row94_zero]
  | succ n ih =>
    have hs : Seg ⟨94,bank b j (n+1) p a w z⟩ ⟨94,bank b j n p (a+1) (w+1) z⟩ 3 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row94_pos,row95,row96]
    have ht : 3*(n+1)+1=3+(3*n+1) := by omega
    have ha : a+1+n=a+(n+1) := by omega
    have hw : w+1+n=w+(n+1) := by omega
    rw [ht,← ha,← hw]
    exact cat hs (ih (a+1) (w+1))

/-- Restore the length from scratch without disturbing the product. -/
theorem restore_length (b : Bank) (j n p a w z : Nat) :
    Seg ⟨97,bank b j n p a w z⟩ ⟨99,bank b j (n+a) p 0 w z⟩ (2*a+1) := by
  induction a generalizing n with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row97_zero]
  | succ a ih =>
    have hs : Seg ⟨97,bank b j n p (a+1) w z⟩ ⟨97,bank b j (n+1) p a w z⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row97_pos,row98]
    have ht : 2*(a+1)+1=2+(2*a+1) := by omega
    have hn : n+1+a=n+(a+1) := by omega
    rw [ht,← hn]
    exact cat hs (ih (n+1))

/-- One unit of the current power adds `n+1` to the product accumulator. -/
theorem product_unit (b : Bank) (j n p w z : Nat) :
    Seg ⟨93,bank b j n (p+1) 0 w z⟩
      ⟨93,bank b j n p 0 (w+(n+1)) z⟩ (5*n+4) := by
  have h₀ : Seg ⟨93,bank b j n (p+1) 0 w z⟩ ⟨94,bank b j n p 0 w z⟩ 1 := by
    simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row93_pos]
  have h₁ := copy_length b j n p 0 w z
  have h₂ := restore_length b j 0 p n (w+n) z
  have h₃ : Seg ⟨99,bank b j n p 0 (w+n) z⟩
      ⟨93,bank b j n p 0 (w+(n+1)) z⟩ 1 := by
    have hx : w+n+1=w+(n+1) := by omega
    simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row99,hx]
  have h := cat (cat (cat h₀ (by simpa using h₁)) (by simpa using h₂)) h₃
  have hc : ((1+(3*n+1))+(2*n+1))+1=5*n+4 := by omega
  simpa only [hc] using h

/-- Repeated addition computes the product and clears the old power. -/
theorem product_drain (b : Bank) (j n p w z : Nat) :
    Seg ⟨93,bank b j n p 0 w z⟩
      ⟨100,bank b j n 0 0 (w+p*(n+1)) z⟩ (p*(5*n+4)+1) := by
  induction p generalizing w with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row93_zero]
  | succ p ih =>
    have hs := product_unit b j n p w z
    have hi := ih (w+(n+1))
    have ht : (p+1)*(5*n+4)+1=(5*n+4)+(p*(5*n+4)+1) := by ring
    have hw : (w+(n+1))+p*(n+1)=w+(p+1)*(n+1) := by ring
    rw [ht,← hw]
    exact cat hs hi

/-- Transfer the product to the power accumulator. -/
theorem product_restore (b : Bank) (j n p w z : Nat) :
    Seg ⟨100,bank b j n p 0 w z⟩ ⟨91,bank b j n (p+w) 0 0 z⟩ (2*w+1) := by
  induction w generalizing p with
  | zero => simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row100_zero]
  | succ w ih =>
    have hs : Seg ⟨100,bank b j n p 0 (w+1) z⟩ ⟨100,bank b j n (p+1) 0 w z⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row100_pos,row101]
    have hp : p+1+w=p+(w+1) := by omega
    have ht : 2*(w+1)+1=2+(2*w+1) := by omega
    rw [ht,← hp]
    exact cat hs (ih (p+1))

def multiplyCost (n p : Nat) : Nat := p*(5*n+4)+1+(2*(p*(n+1))+1)

theorem multiply (b : Bank) (j n p z : Nat) :
    Seg ⟨93,bank b j n p 0 0 z⟩ ⟨91,bank b j n (p*(n+1)) 0 0 z⟩ (multiplyCost n p) := by
  have h₁ := product_drain b j n p 0 z
  have h₂ := product_restore b j n 0 (p*(n+1)) z
  have h := cat h₁ (by simpa using h₂)
  simpa [multiplyCost] using h

end Shared.Beeping.NPcoNP.Source284GraphCandidateClockLoops
