import Shared.Beeping.NPcoNP.Source284GraphBlockPrep
import Shared.Beeping.NPcoNP.Source284GraphApplyCorrect

/-! Block-residence certificates for the decoded-row register loops. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBlockApplyLoops
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphBlockSafety
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem swap_left (b : Bank) (l r s d a w t : Nat) :
    SafeSeg ⟨71,regs b l r s d a w t⟩ ⟨73,regs b 0 r s d a (w+l) t⟩ (2*l+1) := by
  induction l generalizing w with
  | zero => simpa using one _ _ (row71_zero b r s d a w t) (by simp [Inside])
  | succ l ih =>
    have h₁ := one _ _ (row71_positive b l r s d a w t) (by simp [Inside])
    have h₂ := one _ _ (row72 b l r s d a w t) (by simp [Inside])
    have ht : (1+1)+(2*l+1)=2*(l+1)+1 := by omega
    have hw : w+1+l=w+(l+1) := by omega
    simpa only [ht,hw] using cat (cat h₁ h₂) (ih (w+1))

theorem swap_right (b : Bank) (l r s d a w t : Nat) :
    SafeSeg ⟨73,regs b l r s d a w t⟩ ⟨75,regs b (l+r) 0 s d a w t⟩ (2*r+1) := by
  induction r generalizing l with
  | zero => simpa using one _ _ (row73_zero b l s d a w t) (by simp [Inside])
  | succ r ih =>
    have h₁ := one _ _ (row73_positive b l r s d a w t) (by simp [Inside])
    have h₂ := one _ _ (row74 b l r s d a w t) (by simp [Inside])
    have ht : (1+1)+(2*r+1)=2*(r+1)+1 := by omega
    have hl : l+1+r=l+(r+1) := by omega
    simpa only [ht,hl] using cat (cat h₁ h₂) (ih (l+1))

theorem swap_restore (b : Bank) (l r s d a w t : Nat) :
    SafeSeg ⟨75,regs b l r s d a w t⟩ ⟨77,regs b l (r+w) s d a 0 t⟩ (2*w+1) := by
  induction w generalizing r with
  | zero => simpa using one _ _ (row75_zero b l r s d a t) (by simp [Inside])
  | succ w ih =>
    have h₁ := one _ _ (row75_positive b l r s d a w t) (by simp [Inside])
    have h₂ := one _ _ (row76 b l r s d a w t) (by simp [Inside])
    have ht : (1+1)+(2*w+1)=2*(w+1)+1 := by omega
    have hr : r+1+w=r+(w+1) := by omega
    simpa only [ht,hr] using cat (cat h₁ h₂) (ih (r+1))

theorem double_left (b : Bank) (l r s d a w t : Nat) :
    SafeSeg ⟨77,regs b l r s d a w t⟩ ⟨80,regs b 0 r s d a (w+2*l) t⟩ (3*l+1) := by
  induction l generalizing w with
  | zero => simpa using one _ _ (row77_zero b r s d a w t) (by simp [Inside])
  | succ l ih =>
    have h₁ := one _ _ (row77_positive b l r s d a w t) (by simp [Inside])
    have h₂ := one _ _ (row78 b l r s d a w t) (by simp [Inside])
    have h₃ := one _ _ (row79 b l r s d a (w+1) t) (by simp [Inside])
    have ht : ((1+1)+1)+(3*l+1)=3*(l+1)+1 := by omega
    have hw : (w+1+1)+2*l=w+2*(l+1) := by omega
    simpa only [ht,hw] using cat (cat (cat h₁ h₂) h₃) (ih (w+2))

theorem add_write (b : Bank) (l r s d a w t : Nat) :
    SafeSeg ⟨80,regs b l r s d a w t⟩ ⟨82,regs b l r s d 0 (w+a) t⟩ (2*a+1) := by
  induction a generalizing w with
  | zero => simpa using one _ _ (row80_zero b l r s d w t) (by simp [Inside])
  | succ a ih =>
    have h₁ := one _ _ (row80_positive b l r s d a w t) (by simp [Inside])
    have h₂ := one _ _ (row81 b l r s d a w t) (by simp [Inside])
    have ht : (1+1)+(2*a+1)=2*(a+1)+1 := by omega
    have hw : w+1+a=w+(a+1) := by omega
    simpa only [ht,hw] using cat (cat h₁ h₂) (ih (w+1))

theorem write_back (b : Bank) (l r s d a w t : Nat) :
    SafeSeg ⟨83,regs b l r s d a w t⟩ ⟨50,regs b (l+w) r s d a 0 t⟩ (2*w+1) := by
  induction w generalizing l with
  | zero => simpa using one _ _ (row83_zero b l r s d a t) (by simp [Inside])
  | succ w ih =>
    have h₁ := one _ _ (row83_positive b l r s d a w t) (by simp [Inside])
    have h₂ := one _ _ (row84 b l r s d a w t) (by simp [Inside])
    have ht : (1+1)+(2*w+1)=2*(w+1)+1 := by omega
    have hl : l+1+w=l+(w+1) := by omega
    simpa only [ht,hl] using cat (cat h₁ h₂) (ih (l+1))

end Shared.Beeping.NPcoNP.Source284GraphBlockApplyLoops
