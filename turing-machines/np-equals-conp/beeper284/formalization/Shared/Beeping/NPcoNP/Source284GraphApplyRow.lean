import Shared.Beeping.NPcoNP.Source284GraphSkip

/-! Finite register-graph execution of a decoded source row. This is not a
physical binary-tape refinement. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphApplyRow

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284Relative

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def regs (b : Bank) (l r s d a w t : Nat) : Bank :=
  fun i => if i=1 then r else if i=2 then s else if i=6 then d else
    if i=8 then l else if i=9 then a else if i=10 then w else if i=11 then t else b i

@[simp] theorem regs1 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 1 = r := by simp [regs]
@[simp] theorem regs2 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 2 = s := by simp [regs]
@[simp] theorem regs6 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 6 = d := by simp [regs]
@[simp] theorem regs8 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 8 = l := by simp [regs]
@[simp] theorem regs9 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 9 = a := by simp [regs]
@[simp] theorem regs10 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 10 = w := by simp [regs]
@[simp] theorem regs11 (b : Bank) (l r s d a w t : Nat) : regs b l r s d a w t 11 = t := by simp [regs]

theorem write1 (b : Bank) (l r s d a w t v : Nat) : write (regs b l r s d a w t) 1 v = regs b l v s d a w t := by
  funext i; fin_cases i <;> simp [regs,write]
theorem write2 (b : Bank) (l r s d a w t v : Nat) : write (regs b l r s d a w t) 2 v = regs b l r v d a w t := by
  funext i; fin_cases i <;> simp [regs,write]
theorem write8 (b : Bank) (l r s d a w t v : Nat) : write (regs b l r s d a w t) 8 v = regs b v r s d a w t := by
  funext i; fin_cases i <;> simp [regs,write]
theorem write9 (b : Bank) (l r s d a w t v : Nat) : write (regs b l r s d a w t) 9 v = regs b l r s d v w t := by
  funext i; fin_cases i <;> simp [regs,write]
theorem write10 (b : Bank) (l r s d a w t v : Nat) : write (regs b l r s d a w t) 10 v = regs b l r s d a v t := by
  funext i; fin_cases i <;> simp [regs,write]

theorem row68 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨68,regs b l r s d a w t⟩ =
      (⟨if s%2=1 then 69 else 70,regs b l r (s/2) d a w t⟩,[]) := by
  by_cases h : s%2=1
  · simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2,h]
  · have hz : s%2=0 := by omega
    simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2,h,hz]

theorem row69 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨69,regs b l r s d a w t⟩ = (⟨70,regs b l r s d (a+1) w t⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9]

theorem row70 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨70,regs b l r s d a w t⟩ =
      (⟨if s%2=1 then 71 else 77,regs b l r (s/2) d a w t⟩,[]) := by
  by_cases h : s%2=1
  · simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2,h]
  · have hz : s%2=0 := by omega
    simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write2,h,hz]

def decodeCost (row : Nat) : Nat := 2 + row%2

/-- The two flag bits and the next-state quotient are decoded with exact,
positive cost. A set direction bit enters the swap, otherwise the write. -/
theorem decode_flags (b : Bank) (l r row d t : Nat) :
    target.system.advance ⟨68,regs b l r row d 0 0 t⟩ (decodeCost row) =
      ⟨if (row/2)%2=1 then 71 else 77, regs b l r (row/4) d (row%2) 0 t⟩ ∧
    target.system.wordFrom ⟨68,regs b l r row d 0 0 t⟩ (decodeCost row) = [] := by
  have hd : (row/2)/2=row/4 := by omega
  by_cases h : row%2=1
  · simp [decodeCost,h,WordEventSystem.advance,WordEventSystem.wordFrom,row68,row69,row70,hd]
  · have hz : row%2=0 := by omega
    simp [decodeCost,hz,WordEventSystem.advance,WordEventSystem.wordFrom,row68,row70,hd]

theorem row71_positive (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨71,regs b (l+1) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨72,regs b (l) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write8]

theorem row71_zero (b : Bank) (r s d a w t : Nat) :
    target.system.step ⟨71,regs b (0) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨73,regs b (0) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  rfl

theorem row72 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨72,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨71,regs b (l) (r) (s) (d) (a) (w+1) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row73_positive (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨73,regs b (l) (r+1) (s) (d) (a) (w) (t)⟩ =
      (⟨74,regs b (l) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write1]

theorem row73_zero (b : Bank) (l s d a w t : Nat) :
    target.system.step ⟨73,regs b (l) (0) (s) (d) (a) (w) (t)⟩ =
      (⟨75,regs b (l) (0) (s) (d) (a) (w) (t)⟩,[]) := by
  rfl

theorem row74 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨74,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨73,regs b (l+1) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write8]

theorem row75_positive (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨75,regs b (l) (r) (s) (d) (a) (w+1) (t)⟩ =
      (⟨76,regs b (l) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row75_zero (b : Bank) (l r s d a t : Nat) :
    target.system.step ⟨75,regs b (l) (r) (s) (d) (a) (0) (t)⟩ =
      (⟨77,regs b (l) (r) (s) (d) (a) (0) (t)⟩,[]) := by
  rfl

theorem row76 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨76,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨75,regs b (l) (r+1) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write1]

theorem row77_positive (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨77,regs b (l+1) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨78,regs b (l) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write8]

theorem row77_zero (b : Bank) (r s d a w t : Nat) :
    target.system.step ⟨77,regs b (0) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨80,regs b (0) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  rfl

theorem row78 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨78,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨79,regs b (l) (r) (s) (d) (a) (w+1) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row79 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨79,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨77,regs b (l) (r) (s) (d) (a) (w+1) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row80_positive (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨80,regs b (l) (r) (s) (d) (a+1) (w) (t)⟩ =
      (⟨81,regs b (l) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9]

theorem row80_zero (b : Bank) (l r s d w t : Nat) :
    target.system.step ⟨80,regs b (l) (r) (s) (d) (0) (w) (t)⟩ =
      (⟨82,regs b (l) (r) (s) (d) (0) (w) (t)⟩,[]) := by
  rfl

theorem row81 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨81,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨80,regs b (l) (r) (s) (d) (a) (w+1) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row82_zero (b : Bank) (r s d a w t : Nat) :
    target.system.step ⟨82,regs b (0) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨83,regs b (0) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  rfl

theorem row83_positive (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨83,regs b (l) (r) (s) (d) (a) (w+1) (t)⟩ =
      (⟨84,regs b (l) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row83_zero (b : Bank) (l r s d a t : Nat) :
    target.system.step ⟨83,regs b (l) (r) (s) (d) (a) (0) (t)⟩ =
      (⟨50,regs b (l) (r) (s) (d) (a) (0) (t)⟩,[]) := by
  rfl

theorem row84 (b : Bank) (l r s d a w t : Nat) :
    target.system.step ⟨84,regs b (l) (r) (s) (d) (a) (w) (t)⟩ =
      (⟨83,regs b (l+1) (r) (s) (d) (a) (w) (t)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write8]


end Shared.Beeping.NPcoNP.Source284GraphApplyRow
