import Shared.Beeping.NPcoNP.Source284GraphRowStep

/-! Preparation of an arbitrary positive-state source step in the checked
register graph. The clock and all finite register-loop steps are charged. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphPrepStep
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops
open Shared.Beeping.NPcoNP.Source284GraphRowStep
open Shared.Beeping.NPcoNP.Source284Relative
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem write11 (b : Bank) (l r s d a w t v : Nat) :
    write (regs b l r s d a w t) 11 v = regs b l r s d a w v := by
  funext i; fin_cases i <;> simp [regs,write]

theorem row50 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨50,regs b l r s d a w (t+1)⟩ =
      (⟨51,regs b l r s d a w t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write11]

theorem row51 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨51,regs b l r (s+1) d a w t⟩ =
      (⟨52,regs b l r s d a w t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2]

theorem row52 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨52,regs b l r s d a w t⟩ =
      (⟨if r%2=1 then 53 else 54,regs b l (r/2) s d a w t⟩,[]) := by
  by_cases h : r%2=1
  · simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write1,h]
  · have hz : r%2=0 := by omega
    simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write1,h,hz]

theorem row53 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨53,regs b l r s d a w t⟩ =
      (⟨54,regs b l r (s+1) d a w t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2]

/-- Consume the source clock, derive the exact source record index, and
advance past the scanned source bit. -/
theorem head (b : Bank) (l r s d t : Nat) :
    Seg ⟨50,regs b l r (s+1) d 0 0 (t+1)⟩
      ⟨54,regs b l (r/2) (s+r%2) d 0 0 t⟩ (3+r%2) := by
  by_cases h : r%2=1
  · simp [Seg,h,WordEventSystem.advance,WordEventSystem.wordFrom,row50,row51,row52,row53]
  · have hz : r%2=0 := by omega
    simp [Seg,hz,WordEventSystem.advance,WordEventSystem.wordFrom,row50,row51,row52]

/-- Copy the complete description while preserving it, then pass control to
the record lookup. The copy is charged as `5*d+3` register steps. -/
theorem copy_description (b : Bank) (l r s d t : Nat) :
    Seg ⟨54,regs b l r s d 0 0 t⟩ ⟨60,regs b l r s d 0 d t⟩ (5*d+3) := by
  let base := write (write b 8 l) 1 r
  have hd := Source284GraphFirstIteration.drain base s d 0 0 t
  have hr := Source284GraphFirstIteration.restore base s 0 d d t
  have h₁ : Seg ⟨54,regs b l r s d 0 0 t⟩ ⟨57,regs b l r s 0 d d t⟩ (3*d+1) := by
    simpa only [Seg,regs_eq_bank,zero_add] using hd
  have h₂ : Seg ⟨57,regs b l r s 0 d d t⟩ ⟨59,regs b l r s d 0 d t⟩ (2*d+1) := by
    simpa only [Seg,regs_eq_bank,zero_add] using hr
  have h₃ : Seg ⟨59,regs b l r s d 0 d t⟩ ⟨60,regs b l r s d 0 d t⟩ 1 := by
    have h := Source284GraphFirstIteration.row59_zero base s d d t
    dsimp only [base] at h
    simpa [Seg,regs_eq_bank,WordEventSystem.advance,WordEventSystem.wordFrom,h]
  have h := cat (cat h₁ h₂) h₃
  have hc : (3*d+1)+(2*d+1)+1 = 5*d+3 := by omega
  simpa only [hc] using h

def prepareCost (description right : Nat) : Nat := (3+right%2)+(5*description+3)

/-- Explicit, positive, silent preparation of the PC-60 lookup input. -/
theorem prepare (b : Bank) (l r s d t : Nat) :
    Seg ⟨50,regs b l r (s+1) d 0 0 (t+1)⟩
      ⟨60,regs b l (r/2) (s+r%2) d 0 d t⟩ (prepareCost d r) := by
  exact cat (head b l r s d t) (copy_description b l (r/2) (s+r%2) d t)

end Shared.Beeping.NPcoNP.Source284GraphPrepStep
