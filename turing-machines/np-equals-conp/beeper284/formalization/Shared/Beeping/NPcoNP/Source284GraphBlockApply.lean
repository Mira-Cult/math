import Shared.Beeping.NPcoNP.Source284GraphBlockApplyLoops

/-! Block-residence certificate for the complete decoded-row action. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphBlockApply
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyCorrect (swapCost writeCost applyCost leftAfter rightAfter)
open Shared.Beeping.NPcoNP.Source284GraphBlockSafety
open Shared.Beeping.NPcoNP.Source284GraphBlockApplyLoops
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem decode_flags (b : Bank) (l r row d t : Nat) :
    SafeSeg ⟨68,regs b l r row d 0 0 t⟩
      ⟨if (row/2)%2=1 then 71 else 77,regs b l r (row/4) d (row%2) 0 t⟩
      (decodeCost row) := by
  have h₁ := one _ _ (row68 b l r row d 0 0 t) (by simp [Inside])
  have hd : (row/2)/2=row/4 := by omega
  by_cases h : row%2=1
  · have h₁' : SafeSeg ⟨68,regs b l r row d 0 0 t⟩ ⟨69,regs b l r (row/2) d 0 0 t⟩ 1 := by
      simpa [h] using h₁
    have h₂ := one _ _ (row69 b l r (row/2) d 0 0 t) (by simp [Inside])
    have h₃ := one _ _ (row70 b l r (row/2) d 1 0 t) (by simp [Inside])
    simpa [decodeCost,h,hd] using cat (cat h₁' h₂) h₃
  · have hz : row%2=0 := by omega
    have h₁' : SafeSeg ⟨68,regs b l r row d 0 0 t⟩ ⟨70,regs b l r (row/2) d 0 0 t⟩ 1 := by
      simpa [hz] using h₁
    have h₂ := one _ _ (row70 b l r (row/2) d 0 0 t) (by simp [Inside])
    simpa [decodeCost,hz,hd] using cat h₁' h₂

theorem swap (b : Bank) (l r s d a t : Nat) :
    SafeSeg ⟨71,regs b l r s d a 0 t⟩ ⟨77,regs b r l s d a 0 t⟩ (swapCost l r) := by
  have h₁ := swap_left b l r s d a 0 t
  have h₂ := swap_right b 0 r s d a l t
  have h₃ := swap_restore b r 0 s d a l t
  have h := cat (cat h₁ (by simpa using h₂)) (by simpa using h₃)
  simpa [swapCost] using h

theorem write_half (b : Bank) (l r s d bit t : Nat) :
    SafeSeg ⟨77,regs b l r s d bit 0 t⟩
      ⟨50,regs b (2*l+bit) r s d 0 0 t⟩ (writeCost l bit) := by
  have h₁ := double_left b l r s d bit 0 t
  have h₂ := add_write b 0 r s d bit (2*l) t
  have h₃ := one _ _ (row82_zero b r s d 0 (2*l+bit) t) (by simp [Inside])
  have h₄ := write_back b 0 r s d 0 (2*l+bit) t
  have h := cat (cat (cat h₁ (by simpa using h₂)) h₃) h₄
  simpa [writeCost] using h

/-- The entire decoded-row action stays in the evaluator block until its
return to PC 50. -/
theorem apply (b : Bank) (l r row d t : Nat) :
    SafeSeg ⟨68,regs b l r row d 0 0 t⟩
      ⟨50,regs b (leftAfter row l r) (rightAfter row l r) (row/4) d 0 0 t⟩
      (applyCost row l r) := by
  have hd := decode_flags b l r row d t
  by_cases h : (row/2)%2=1
  · have hd' : SafeSeg ⟨68,regs b l r row d 0 0 t⟩
        ⟨71,regs b l r (row/4) d (row%2) 0 t⟩ (decodeCost row) := by simpa [h] using hd
    have hs := swap b l r (row/4) d (row%2) t
    have hw := write_half b r l (row/4) d (row%2) t
    simpa [applyCost,leftAfter,rightAfter,h] using cat hd' (cat hs hw)
  · have hd' : SafeSeg ⟨68,regs b l r row d 0 0 t⟩
        ⟨77,regs b l r (row/4) d (row%2) 0 t⟩ (decodeCost row) := by simpa [h] using hd
    have hw := write_half b l r (row/4) d (row%2) t
    simpa [applyCost,leftAfter,rightAfter,h] using cat hd' hw

end Shared.Beeping.NPcoNP.Source284GraphBlockApply
