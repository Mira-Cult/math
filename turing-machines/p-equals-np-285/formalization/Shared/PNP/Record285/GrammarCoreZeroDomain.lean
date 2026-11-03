import Shared.PNP.Record285.GrammarCoreGraph

/-! A three-category abstract domain for the pre-elimination core graph.
The representative theorem covers all naturals, not a finite test range. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.Grammar

def category (n : Nat) : Nat := if n = 0 then 0 else if n = 1 then 1 else 2

def admits (mask value : Nat) : Bool :=
  decide ((mask / 2^(category value)) % 2 = 1)

theorem category_lt_three (n : Nat) : category n < 3 := by
  by_cases h0 : n = 0
  · simp [category,h0]
  · by_cases h1 : n = 1 <;> simp [category,h0,h1]

theorem category_idempotent (n : Nat) : category (category n) = category n := by
  unfold category
  split <;> split <;> simp_all

theorem admits_category (mask value : Nat) : admits mask (category value) = admits mask value := by
  simp [admits,category_idempotent]

/-- Six representatives preserve zero/one/many, parity, and the relevant
post-operation category for increment, saturating decrement and halving. -/
def representative (n : Nat) : Nat :=
  if n < 4 then n else if n % 2 = 0 then 4 else 5

theorem representative_lt_six (n : Nat) : representative n < 6 := by
  by_cases h : n < 4
  · simp [representative,h]; omega
  · by_cases hp : n % 2 = 0 <;> simp [representative,h,hp]

theorem representative_category (n : Nat) : category (representative n) = category n := by
  by_cases h : n < 4
  · simp [representative,h]
  · have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    by_cases hp : n % 2 = 0 <;> simp [representative,h,hp,category,h0,h1]

theorem representative_inc (n : Nat) :
    category (representative n + 1) = category (n+1) := by
  by_cases h : n < 4
  · simp [representative,h]
  · have h0 : n ≠ 0 := by omega
    by_cases hp : n % 2 = 0 <;> simp [representative,h,hp,category,h0]

theorem representative_dec (n : Nat) :
    category (representative n - 1) = category (n-1) := by
  by_cases h : n < 4
  · simp [representative,h]
  · have h0 : n-1 ≠ 0 := by omega
    have h1 : n-1 ≠ 1 := by omega
    by_cases hp : n % 2 = 0 <;> simp [representative,h,hp,category,h0,h1]

theorem representative_half (n : Nat) :
    category (representative n / 2) = category (n/2) := by
  by_cases h : n < 4
  · simp [representative,h]
  · have h0 : n/2 ≠ 0 := by omega
    have h1 : n/2 ≠ 1 := by omega
    by_cases hp : n % 2 = 0 <;> simp [representative,h,hp,category,h0,h1]

theorem representative_zero (n : Nat) : (representative n = 0) ↔ n = 0 := by
  by_cases h : n < 4
  · simp [representative,h]
  · have h0 : n ≠ 0 := by omega
    by_cases hp : n % 2 = 0 <;> simp [representative,h,hp,h0]

theorem representative_parity (n : Nat) : representative n % 2 = n % 2 := by
  by_cases h : n < 4
  · simp [representative,h]
  · by_cases hp : n % 2 = 0
    · simp [representative,h,hp]
    · have hp' : n % 2 = 1 := by omega
      simp [representative,h,hp']

theorem admits_representative (mask n : Nat) : admits mask (representative n) = admits mask n := by
  simp [admits,representative_category]

def operationValue : Edge → Nat → Nat
  | .inc _, n => n+1
  | .dec _, n => n-1
  | .half _, n => n/2
  | _, n => n

def operationIndex : Edge → Option Nat
  | .inc i | .dec i | .half i => some i
  | _ => none

def operationBranch : Edge → Nat → Bool
  | .dec _, n => decide (n = 0)
  | .half _, n => decide (n % 2 = 0)
  | _, _ => false

theorem representative_operation (e : Edge) (n : Nat) :
    category (operationValue e (representative n)) = category (operationValue e n) := by
  cases e <;> simp [operationValue,representative_inc,representative_dec,
    representative_half,representative_category]

theorem representative_branch (e : Edge) (n : Nat) :
    operationBranch e (representative n) = operationBranch e n := by
  cases e <;> simp [operationBranch,representative_zero,representative_parity]

theorem admits_operation_representative (mask : Nat) (e : Edge) (n : Nat) :
    admits mask (operationValue e (representative n)) = admits mask (operationValue e n) := by
  simp [admits,representative_operation]

end Shared.PNP.Record285.GrammarCoreZero
