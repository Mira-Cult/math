import Shared.Beeping.NPcoNP.Source284GraphCandidateHandoff

/-! Concrete graph rows for constructing the candidate certificate bound. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateBoundRows
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
abbrev Bank := PASoundness.RegisterMachine.Bank 12

def bank (b : Bank) (p h w z : Nat) : Bank :=
  fun i => if i=6 then p else if i=7 then h else if i=10 then w else if i=11 then z else b i

@[simp] theorem bank6 (b : Bank) (p h w z : Nat) : bank b p h w z 6=p := by simp [bank]
@[simp] theorem bank7 (b : Bank) (p h w z : Nat) : bank b p h w z 7=h := by simp [bank]
@[simp] theorem bank10 (b : Bank) (p h w z : Nat) : bank b p h w z 10=w := by simp [bank]
@[simp] theorem bank11 (b : Bank) (p h w z : Nat) : bank b p h w z 11=z := by simp [bank]
theorem write6 (b : Bank) (p h w z v : Nat) : write (bank b p h w z) 6 v = bank b v h w z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write7 (b : Bank) (p h w z v : Nat) : write (bank b p h w z) 7 v = bank b p v w z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write10 (b : Bank) (p h w z v : Nat) : write (bank b p h w z) 10 v = bank b p h v z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write11 (b : Bank) (p h w z v : Nat) : write (bank b p h w z) 11 v = bank b p h w v := by
  funext i; fin_cases i <;> simp [bank,write]

theorem row104_pos (b : Bank) (p h w z : Nat) :
    target.system.step ⟨104,bank b (p) (h+1) (w) (z)⟩ = (⟨104,bank b (p) (h) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write7]

theorem row104_zero (b : Bank) (p w z : Nat) :
    target.system.step ⟨104,bank b (p) (0) (w) (z)⟩ = (⟨105,bank b (p) (0) (w) (z)⟩,[]) := by
  rfl

theorem row105 (b : Bank) (p h w z : Nat) :
    target.system.step ⟨105,bank b (p) (h) (w) (z)⟩ = (⟨106,bank b (p) (h+1) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write7]

theorem row106_pos (b : Bank) (p h w z : Nat) :
    target.system.step ⟨106,bank b (p+1) (h) (w) (z)⟩ = (⟨107,bank b (p) (h) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write6]

theorem row106_zero (b : Bank) (h w z : Nat) :
    target.system.step ⟨106,bank b (0) (h) (w) (z)⟩ = (⟨113,bank b (0) (h) (w) (z)⟩,[]) := by
  rfl

theorem row107 (b : Bank) (p h w z : Nat) :
    target.system.step ⟨107,bank b (p) (h) (w) (z)⟩ = (⟨108,bank b (p) (h) (w) (z+1)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write11]

theorem row108_pos (b : Bank) (p h w z : Nat) :
    target.system.step ⟨108,bank b (p) (h+1) (w) (z)⟩ = (⟨109,bank b (p) (h) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write7]

theorem row108_zero (b : Bank) (p w z : Nat) :
    target.system.step ⟨108,bank b (p) (0) (w) (z)⟩ = (⟨111,bank b (p) (0) (w) (z)⟩,[]) := by
  rfl

theorem row109 (b : Bank) (p h w z : Nat) :
    target.system.step ⟨109,bank b (p) (h) (w) (z)⟩ = (⟨110,bank b (p) (h) (w+1) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row110 (b : Bank) (p h w z : Nat) :
    target.system.step ⟨110,bank b (p) (h) (w) (z)⟩ = (⟨108,bank b (p) (h) (w+1) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row111_pos (b : Bank) (p h w z : Nat) :
    target.system.step ⟨111,bank b (p) (h) (w+1) (z)⟩ = (⟨112,bank b (p) (h) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row111_zero (b : Bank) (p h z : Nat) :
    target.system.step ⟨111,bank b (p) (h) (0) (z)⟩ = (⟨106,bank b (p) (h) (0) (z)⟩,[]) := by
  rfl

theorem row112 (b : Bank) (p h w z : Nat) :
    target.system.step ⟨112,bank b (p) (h) (w) (z)⟩ = (⟨111,bank b (p) (h+1) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write7]

theorem row113_pos (b : Bank) (p h w z : Nat) :
    target.system.step ⟨113,bank b (p) (h) (w) (z+1)⟩ = (⟨114,bank b (p) (h) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write11]

theorem row113_zero (b : Bank) (p h w : Nat) :
    target.system.step ⟨113,bank b (p) (h) (w) (0)⟩ = (⟨115,bank b (p) (h) (w) (0)⟩,[]) := by
  rfl

theorem row114 (b : Bank) (p h w z : Nat) :
    target.system.step ⟨114,bank b (p) (h) (w) (z)⟩ = (⟨113,bank b (p+1) (h) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write6]

end Shared.Beeping.NPcoNP.Source284GraphCandidateBoundRows
