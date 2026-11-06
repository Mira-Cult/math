import Shared.Beeping.NPcoNP.Source284GraphApplyRow

/-! Charged silent register loops used to apply one decoded source row. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphApplyLoops

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow

abbrev Cfg := PASoundness.RegisterMachine.Config 12 185
abbrev Bank := PASoundness.RegisterMachine.Bank 12

def Seg (a b : Cfg) (n : Nat) : Prop :=
  target.system.advance a n = b ∧ target.system.wordFrom a n = []

theorem cat {a b c : Cfg} {n m : Nat} (h₁ : Seg a b n) (h₂ : Seg b c m) : Seg a c (n+m) := by
  constructor
  · rw [WordEventSystem.advance_add,h₁.1,h₂.1]
  · rw [WordEventSystem.wordFrom_add,h₁.1,h₁.2,h₂.2]; rfl

/-- Move the entire left half to scratch register 10. -/
theorem swap_left (b : Bank) (l r s d a w t : Nat) :
    Seg ⟨71,regs b l r s d a w t⟩ ⟨73,regs b 0 r s d a (w+l) t⟩ (2*l+1) := by
  induction l generalizing w with
  | zero => simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row71_zero]
  | succ l ih =>
    have h : Seg ⟨71,regs b (l+1) r s d a w t⟩ ⟨71,regs b l r s d a (w+1) t⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row71_positive,row72]
    have hx : w+1+l=w+(l+1) := by omega
    have ht : 2*(l+1)+1=2+(2*l+1) := by omega
    rw [ht,← hx]
    exact cat h (ih (w+1))

/-- Move the old right half into the now-empty left half. -/
theorem swap_right (b : Bank) (l r s d a w t : Nat) :
    Seg ⟨73,regs b l r s d a w t⟩ ⟨75,regs b (l+r) 0 s d a w t⟩ (2*r+1) := by
  induction r generalizing l with
  | zero => simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row73_zero]
  | succ r ih =>
    have h : Seg ⟨73,regs b l (r+1) s d a w t⟩ ⟨73,regs b (l+1) r s d a w t⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row73_positive,row74]
    have hx : l+1+r=l+(r+1) := by omega
    have ht : 2*(r+1)+1=2+(2*r+1) := by omega
    rw [ht,← hx]
    exact cat h (ih (l+1))

/-- Restore the saved left half into the right half. -/
theorem swap_restore (b : Bank) (l r s d a w t : Nat) :
    Seg ⟨75,regs b l r s d a w t⟩ ⟨77,regs b l (r+w) s d a 0 t⟩ (2*w+1) := by
  induction w generalizing r with
  | zero => simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row75_zero]
  | succ w ih =>
    have h : Seg ⟨75,regs b l r s d a (w+1) t⟩ ⟨75,regs b l (r+1) s d a w t⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row75_positive,row76]
    have hx : r+1+w=r+(w+1) := by omega
    have ht : 2*(w+1)+1=2+(2*w+1) := by omega
    rw [ht,← hx]
    exact cat h (ih (r+1))

/-- Double the left half into scratch. -/
theorem double_left (b : Bank) (l r s d a w t : Nat) :
    Seg ⟨77,regs b l r s d a w t⟩ ⟨80,regs b 0 r s d a (w+2*l) t⟩ (3*l+1) := by
  induction l generalizing w with
  | zero => simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row77_zero]
  | succ l ih =>
    have h : Seg ⟨77,regs b (l+1) r s d a w t⟩ ⟨77,regs b l r s d a (w+2) t⟩ 3 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row77_positive,row78,row79]
    have hx : w+2+2*l=w+2*(l+1) := by omega
    have ht : 3*(l+1)+1=3+(3*l+1) := by omega
    rw [ht,← hx]
    exact cat h (ih (w+2))

/-- Add the decoded write bit to the doubled half. -/
theorem add_write (b : Bank) (l r s d a w t : Nat) :
    Seg ⟨80,regs b l r s d a w t⟩ ⟨82,regs b l r s d 0 (w+a) t⟩ (2*a+1) := by
  induction a generalizing w with
  | zero => simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row80_zero]
  | succ a ih =>
    have h : Seg ⟨80,regs b l r s d (a+1) w t⟩ ⟨80,regs b l r s d a (w+1) t⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row80_positive,row81]
    have hx : w+1+a=w+(a+1) := by omega
    have ht : 2*(a+1)+1=2+(2*a+1) := by omega
    rw [ht,← hx]
    exact cat h (ih (w+1))

/-- Move the updated half back and return to the source evaluator loop. -/
theorem write_back (b : Bank) (l r s d a w t : Nat) :
    Seg ⟨83,regs b l r s d a w t⟩ ⟨50,regs b (l+w) r s d a 0 t⟩ (2*w+1) := by
  induction w generalizing l with
  | zero => simpa [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row83_zero]
  | succ w ih =>
    have h : Seg ⟨83,regs b l r s d a (w+1) t⟩ ⟨83,regs b (l+1) r s d a w t⟩ 2 := by
      simp [Seg,WordEventSystem.advance,WordEventSystem.wordFrom,row83_positive,row84]
    have hx : l+1+w=l+(w+1) := by omega
    have ht : 2*(w+1)+1=2+(2*w+1) := by omega
    rw [ht,← hx]
    exact cat h (ih (l+1))

end Shared.Beeping.NPcoNP.Source284GraphApplyLoops
