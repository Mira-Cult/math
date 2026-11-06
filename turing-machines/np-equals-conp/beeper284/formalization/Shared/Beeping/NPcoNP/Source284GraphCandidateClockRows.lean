import Shared.Beeping.NPcoNP.Source284GraphReferenceComplete

/-! Concrete candidate-clock instructions in the pinned coalesced graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateClockRows
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
abbrev Bank := PASoundness.RegisterMachine.Bank 12

def bank (b : Bank) (j n p a w z : Nat) : Bank :=
  fun i => if i=3 then j else if i=5 then n else if i=6 then p else
    if i=9 then a else if i=10 then w else if i=11 then z else b i

@[simp] theorem bank3 (b : Bank) (j n p a w z : Nat) : bank b j n p a w z 3=j := by simp [bank]
@[simp] theorem bank5 (b : Bank) (j n p a w z : Nat) : bank b j n p a w z 5=n := by simp [bank]
@[simp] theorem bank6 (b : Bank) (j n p a w z : Nat) : bank b j n p a w z 6=p := by simp [bank]
@[simp] theorem bank9 (b : Bank) (j n p a w z : Nat) : bank b j n p a w z 9=a := by simp [bank]
@[simp] theorem bank10 (b : Bank) (j n p a w z : Nat) : bank b j n p a w z 10=w := by simp [bank]
@[simp] theorem bank11 (b : Bank) (j n p a w z : Nat) : bank b j n p a w z 11=z := by simp [bank]

theorem write3 (b : Bank) (j n p a w z v : Nat) : write (bank b j n p a w z) 3 v = bank b v n p a w z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write5 (b : Bank) (j n p a w z v : Nat) : write (bank b j n p a w z) 5 v = bank b j v p a w z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write6 (b : Bank) (j n p a w z v : Nat) : write (bank b j n p a w z) 6 v = bank b j n v a w z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write9 (b : Bank) (j n p a w z v : Nat) : write (bank b j n p a w z) 9 v = bank b j n p v w z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write10 (b : Bank) (j n p a w z v : Nat) : write (bank b j n p a w z) 10 v = bank b j n p a v z := by
  funext i; fin_cases i <;> simp [bank,write]
theorem write11 (b : Bank) (j n p a w z v : Nat) : write (bank b j n p a w z) 11 v = bank b j n p a w v := by
  funext i; fin_cases i <;> simp [bank,write]

theorem row89_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨89,bank b (j) (n) (p+1) (a) (w) (z)⟩ = (⟨89,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write6]

theorem row89_zero (b : Bank) (j n a w z : Nat) :
    target.system.step ⟨89,bank b (j) (n) (0) (a) (w) (z)⟩ = (⟨90,bank b (j) (n) (0) (a) (w) (z)⟩,[]) := by
  rfl

theorem row90 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨90,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨91,bank b (j) (n) (p+1) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write6]

theorem row91_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨91,bank b (j+1) (n) (p) (a) (w) (z)⟩ = (⟨92,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write3]

theorem row91_zero (b : Bank) (n p a w z : Nat) :
    target.system.step ⟨91,bank b (0) (n) (p) (a) (w) (z)⟩ = (⟨102,bank b (0) (n) (p) (a) (w) (z)⟩,[]) := by
  rfl

theorem row92 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨92,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨93,bank b (j) (n) (p) (a) (w) (z+1)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write11]

theorem row93_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨93,bank b (j) (n) (p+1) (a) (w) (z)⟩ = (⟨94,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write6]

theorem row93_zero (b : Bank) (j n a w z : Nat) :
    target.system.step ⟨93,bank b (j) (n) (0) (a) (w) (z)⟩ = (⟨100,bank b (j) (n) (0) (a) (w) (z)⟩,[]) := by
  rfl

theorem row94_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨94,bank b (j) (n+1) (p) (a) (w) (z)⟩ = (⟨95,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write5]

theorem row94_zero (b : Bank) (j p a w z : Nat) :
    target.system.step ⟨94,bank b (j) (0) (p) (a) (w) (z)⟩ = (⟨97,bank b (j) (0) (p) (a) (w) (z)⟩,[]) := by
  rfl

theorem row95 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨95,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨96,bank b (j) (n) (p) (a) (w+1) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row96 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨96,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨94,bank b (j) (n) (p) (a+1) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9]

theorem row97_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨97,bank b (j) (n) (p) (a+1) (w) (z)⟩ = (⟨98,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write9]

theorem row97_zero (b : Bank) (j n p w z : Nat) :
    target.system.step ⟨97,bank b (j) (n) (p) (0) (w) (z)⟩ = (⟨99,bank b (j) (n) (p) (0) (w) (z)⟩,[]) := by
  rfl

theorem row98 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨98,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨97,bank b (j) (n+1) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write5]

theorem row99 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨99,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨93,bank b (j) (n) (p) (a) (w+1) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row100_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨100,bank b (j) (n) (p) (a) (w+1) (z)⟩ = (⟨101,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write10]

theorem row100_zero (b : Bank) (j n p a z : Nat) :
    target.system.step ⟨100,bank b (j) (n) (p) (a) (0) (z)⟩ = (⟨91,bank b (j) (n) (p) (a) (0) (z)⟩,[]) := by
  rfl

theorem row101 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨101,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨100,bank b (j) (n) (p+1) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write6]

theorem row102_pos (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨102,bank b (j) (n) (p) (a) (w) (z+1)⟩ = (⟨103,bank b (j) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write11]

theorem row102_zero (b : Bank) (j n p a w : Nat) :
    target.system.step ⟨102,bank b (j) (n) (p) (a) (w) (0)⟩ = (⟨104,bank b (j) (n) (p) (a) (w) (0)⟩,[]) := by
  rfl

theorem row103 (b : Bank) (j n p a w z : Nat) :
    target.system.step ⟨103,bank b (j) (n) (p) (a) (w) (z)⟩ = (⟨102,bank b (j+1) (n) (p) (a) (w) (z)⟩,[]) := by
  simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,
    Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix,write3]

end Shared.Beeping.NPcoNP.Source284GraphCandidateClockRows
