import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! Finite, silent reference-branch initialization in the checked
185-row register graph. This assumes the supplied entry configuration and
does not prove physical-table reachability or complete comparison correctness. -/
namespace Shared.Beeping.NPcoNP.Source284GraphBranchCopy
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def bank (b : Bank) (x y z w : Nat) : Bank :=
  fun i => if i = 6 then x else if i = 9 then y else if i = 10 then z else if i = 7 then w else b i

@[simp] theorem bank6 (b : Bank) (x y z w : Nat) : bank b x y z w 6 = x := by simp [bank]
@[simp] theorem bank9 (b : Bank) (x y z w : Nat) : bank b x y z w 9 = y := by simp [bank]
@[simp] theorem bank10 (b : Bank) (x y z w : Nat) : bank b x y z w 10 = z := by simp [bank]
@[simp] theorem bank7 (b : Bank) (x y z w : Nat) : bank b x y z w 7 = w := by simp [bank]
@[simp] theorem bank_same (b : Bank) : bank b (b 6) (b 9) (b 10) (b 7) = b := by
  funext i; fin_cases i <;> simp [bank]

theorem write6 (b : Bank) (x y z w a : Nat) : write (bank b x y z w) 6 a = bank b a y z w := by
  funext i; fin_cases i <;> simp [write,bank]
theorem write9 (b : Bank) (x y z w a : Nat) : write (bank b x y z w) 9 a = bank b x a z w := by
  funext i; fin_cases i <;> simp [write,bank]
theorem write10 (b : Bank) (x y z w a : Nat) : write (bank b x y z w) 10 a = bank b x y a w := by
  funext i; fin_cases i <;> simp [write,bank]
theorem write7 (b : Bank) (x y z w a : Nat) : write (bank b x y z w) 7 a = bank b x y z a := by
  funext i; fin_cases i <;> simp [write,bank]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

macro "literal_simp" : tactic => `(tactic| simp [target, MaskInvariant.Program.system,
    MaskInvariant.Action.execute, Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix,
    PASoundness.RegisterMachine.execute, write6, write9, write10, write7])

theorem step23_pos (b : Bank) (x y z w : Nat) :
    target.system.step ⟨23,bank b (x+1) y z w⟩ = (⟨24,bank b x y z w⟩,[]) := by literal_simp

theorem step23_zero (b : Bank) (y z w : Nat) :
    target.system.step ⟨23,bank b 0 y z w⟩ = (⟨26,bank b 0 y z w⟩,[]) := by rfl

theorem step24 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨24,bank b x y z w⟩ = (⟨25,bank b x y (z+1) w⟩,[]) := by literal_simp

theorem step25 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨25,bank b x y z w⟩ = (⟨23,bank b x (y+1) z w⟩,[]) := by literal_simp

theorem step26_pos (b : Bank) (x y z w : Nat) :
    target.system.step ⟨26,bank b x (y+1) z w⟩ = (⟨27,bank b x y z w⟩,[]) := by literal_simp

theorem step26_zero (b : Bank) (x z w : Nat) :
    target.system.step ⟨26,bank b x 0 z w⟩ = (⟨28,bank b x 0 z w⟩,[]) := by rfl

theorem step27 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨27,bank b x y z w⟩ = (⟨26,bank b (x+1) y z w⟩,[]) := by literal_simp

theorem step28_pos (b : Bank) (x y z w : Nat) :
    target.system.step ⟨28,bank b x y z (w+1)⟩ = (⟨28,bank b x y z w⟩,[]) := by literal_simp

theorem step28_zero (b : Bank) (x y z : Nat) :
    target.system.step ⟨28,bank b x y z 0⟩ = (⟨29,bank b x y z 0⟩,[]) := by rfl

theorem step29_pos (b : Bank) (x y z w : Nat) :
    target.system.step ⟨29,bank b x y (z+1) w⟩ = (⟨30,bank b x y z w⟩,[]) := by literal_simp

theorem step29_zero (b : Bank) (x y w : Nat) :
    target.system.step ⟨29,bank b x y 0 w⟩ = (⟨31,bank b x y 0 w⟩,[]) := by rfl

theorem step30 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨30,bank b x y z w⟩ = (⟨29,bank b x y z (w+1)⟩,[]) := by literal_simp

/-- Transfer register 6 into both scratch registers. -/
theorem drain (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨23,bank b x y z w⟩ (3*x+1) = ⟨26,bank b 0 (y+x) (z+x) w⟩ ∧
    target.system.wordFrom ⟨23,bank b x y z w⟩ (3*x+1) = [] := by
  induction x generalizing y z with
  | zero => simp [WordEventSystem.advance,WordEventSystem.wordFrom,step23_zero]
  | succ x ih =>
    have hs : target.system.advance ⟨23,bank b (x+1) y z w⟩ 3 = ⟨23,bank b x (y+1) (z+1) w⟩ ∧
        target.system.wordFrom ⟨23,bank b (x+1) y z w⟩ 3 = [] := by
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,step23_pos,step24,step25]
    have hi := ih (y+1) (z+1)
    have ht : 3*(x+1)+1 = 3+(3*x+1) := by omega
    constructor
    · rw [ht,WordEventSystem.advance_add,hs.1,hi.1]; congr 2 <;> omega
    · rw [ht,WordEventSystem.wordFrom_add,hs.1,hs.2,hi.2]; rfl

/-- Restore register 6 from register 9. -/
theorem restore (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨26,bank b x y z w⟩ (2*y+1) = ⟨28,bank b (x+y) 0 z w⟩ ∧
    target.system.wordFrom ⟨26,bank b x y z w⟩ (2*y+1) = [] := by
  induction y generalizing x with
  | zero => simp [WordEventSystem.advance,WordEventSystem.wordFrom,step26_zero]
  | succ y ih =>
    have hs : target.system.advance ⟨26,bank b x (y+1) z w⟩ 2 = ⟨26,bank b (x+1) y z w⟩ ∧
        target.system.wordFrom ⟨26,bank b x (y+1) z w⟩ 2 = [] := by
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,step26_pos,step27]
    have hi := ih (x+1)
    have ht : 2*(y+1)+1 = 2+(2*y+1) := by omega
    constructor
    · rw [ht,WordEventSystem.advance_add,hs.1,hi.1]; congr 2 <;> omega
    · rw [ht,WordEventSystem.wordFrom_add,hs.1,hs.2,hi.2]; rfl

/-- Clear the old branch register. -/
theorem clear (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨28,bank b x y z w⟩ (w+1) = ⟨29,bank b x y z 0⟩ ∧
    target.system.wordFrom ⟨28,bank b x y z w⟩ (w+1) = [] := by
  induction w with
  | zero => simp [WordEventSystem.advance,WordEventSystem.wordFrom,step28_zero]
  | succ w ih =>
    have ht : w+1+1 = 1+(w+1) := by omega
    have hs : target.system.advance ⟨28,bank b x y z (w+1)⟩ 1 = ⟨28,bank b x y z w⟩ := by
      simp [WordEventSystem.advance, step28_pos]
    have hw : target.system.wordFrom ⟨28,bank b x y z (w+1)⟩ 1 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step28_pos]
    constructor
    · rw [ht,WordEventSystem.advance_add, hs, ih.1]
    · rw [ht,WordEventSystem.wordFrom_add, hs, hw, ih.2]; rfl

/-- Transfer register 10 into the now-empty branch register. -/
theorem fill (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨29,bank b x y z w⟩ (2*z+1) = ⟨31,bank b x y 0 (w+z)⟩ ∧
    target.system.wordFrom ⟨29,bank b x y z w⟩ (2*z+1) = [] := by
  induction z generalizing w with
  | zero => simp [WordEventSystem.advance,WordEventSystem.wordFrom,step29_zero]
  | succ z ih =>
    have hs : target.system.advance ⟨29,bank b x y (z+1) w⟩ 2 = ⟨29,bank b x y z (w+1)⟩ ∧
        target.system.wordFrom ⟨29,bank b x y (z+1) w⟩ 2 = [] := by
      simp [WordEventSystem.advance,WordEventSystem.wordFrom,step29_pos,step30]
    have hi := ih (w+1)
    have ht : 2*(z+1)+1 = 2+(2*z+1) := by omega
    constructor
    · rw [ht,WordEventSystem.advance_add,hs.1,hi.1]; congr 2 <;> omega
    · rw [ht,WordEventSystem.wordFrom_add,hs.1,hs.2,hi.2]; rfl

abbrev Cfg := PASoundness.RegisterMachine.Config 12 185

def SilentSegment (a z : Cfg) (k : Nat) : Prop :=
  target.system.advance a k = z ∧ target.system.wordFrom a k = []

theorem cat {a b c : Cfg} {k l : Nat}
    (h : SilentSegment a b k) (g : SilentSegment b c l) : SilentSegment a c (k+l) := by
  rcases h with ⟨ha, hw⟩
  rcases g with ⟨ga, gw⟩
  constructor
  · rw [WordEventSystem.advance_add, ha, ga]
  · rw [WordEventSystem.wordFrom_add, ha, hw, gw]; rfl

/-- With both scratch registers zero, initialize the reference certificate
counter to the parser description while retaining that description. -/
theorem branch_copy (b : Bank) (h9 : b 9 = 0) (h10 : b 10 = 0) :
    let d := 7*b 6+b 7+4
    target.system.advance ⟨23,b⟩ d = ⟨31,write b 7 (b 6)⟩ ∧
      target.system.wordFrom ⟨23,b⟩ d = [] ∧ 0 < d := by
  have hb : bank b (b 6) 0 0 (b 7) = b := by simpa [h9,h10] using bank_same b
  have hd := drain b (b 6) 0 0 (b 7)
  simp only [Nat.zero_add, hb] at hd
  have hr := restore b 0 (b 6) (b 6) (b 7)
  have hc := clear b (b 6) 0 (b 6) (b 7)
  have hf := fill b (b 6) 0 (b 6) 0
  have he : bank b (b 6) 0 0 (b 6) = write b 7 (b 6) := by
    rw [← write7 b (b 6) 0 0 (b 7) (b 6),hb]
  have ht : 7*b 6+b 7+4 = ((3*b 6+1)+(2*b 6+1))+(b 7+1)+(2*b 6+1) := by omega
  simp only [Nat.zero_add] at hr hf
  have h := cat (cat (cat hd hr) hc) hf
  rw [← ht, he] at h
  exact ⟨h.1, h.2, by omega⟩
end Shared.Beeping.NPcoNP.Source284GraphBranchCopy
