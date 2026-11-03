import Shared.PNP.Record285.GrammarCoreZeroCheck

/-! Soundness of the finite mask transfer checker over arbitrary naturals. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph

theorem subset_sound (a b n : Nat) (h : subset a b = true) (ha : admits a n = true) :
    admits b n = true := by
  have hi : category n ∈ List.range 3 := List.mem_range.mpr (category_lt_three n)
  have hcase := List.all_eq_true.mp h (category n) hi
  simp only [admits_category,ha,Bool.not_true,Bool.false_or] at hcase
  exact hcase

theorem otherSlots_sound (before after : Array Nat) (except i value : Nat)
    (h : otherSlots before after except = true) (hi : i < 15) (hne : i ≠ except)
    (hadmit : admits (slot before i) value = true) :
    admits (slot after i) value = true := by
  have hcase := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  have hsub : subset (slot before i) (slot after i) = true := by simpa [hne] using hcase
  exact subset_sound _ _ _ hsub hadmit

/-- For every natural input, not just its finite representative, a checked
branch preserves the target category and all other register masks. -/
theorem branchCheck_sound (e : Edge) (i : Nat) (before after : Array Nat) (branch : Bool)
    (h : branchCheck e i before after branch = true) (value : Nat)
    (hadmit : admits (slot before i) value = true)
    (hbranch : operationBranch e value = branch) :
    admits (slot after i) (operationValue e value) = true ∧
      ∀ j, j < 15 → j ≠ i → ∀ x, admits (slot before j) x = true → admits (slot after j) x = true := by
  let rep := representative value
  have hrep : rep ∈ List.range 6 := List.mem_range.mpr (representative_lt_six value)
  have hcase := List.all_eq_true.mp h rep hrep
  have hinput : admits (slot before i) rep = true := by
    simpa only [rep,admits_representative] using hadmit
  have htest : operationBranch e rep = branch := by
    simpa only [rep,representative_branch] using hbranch
  simp only [hinput,htest,beq_self_eq_true,Bool.true_and,if_true,
    Bool.and_eq_true_iff] at hcase
  constructor
  · simpa only [rep,admits_operation_representative] using hcase.1
  · intro j hj hne x hx
    exact otherSlots_sound before after i j x hcase.2 hj hne hx

def operandValue (e : Edge) (bank : Nat → Nat) : Nat :=
  match operationIndex e with
  | some i => bank i
  | none => 0

def updateBank (e : Edge) (bank : Nat → Nat) (j : Nat) : Nat :=
  match operationIndex e with
  | some i => if j = i then operationValue e (bank i) else bank j
  | none => bank j

def validBank (mask : Array Nat) (bank : Nat → Nat) : Prop :=
  ∀ j, j < 15 → admits (slot mask j) (bank j) = true

/-- A certified abstract transfer preserves every one of the fifteen bank
values, for an arbitrary natural-valued bank. -/
theorem transfers_sound (spec : CoreRow) (before no yes : Array Nat) (bank : Nat → Nat)
    (h : transfers spec before no yes = true) (hbank : validBank before bank) :
    validBank (if operationBranch spec.edge (operandValue spec.edge bank) then yes else no)
      (updateBank spec.edge bank) := by
  cases hi : operationIndex spec.edge with
  | none =>
    by_cases hb : spec.edge = .beep
    · have hother : otherSlots before no 15 = true := by simpa [transfers,hb,operationIndex] using h
      intro j hj
      have hne : j ≠ 15 := by omega
      have hv := otherSlots_sound before no 15 j (bank j) hother hj hne (hbank j hj)
      simpa [hb,operandValue,operationBranch,updateBank,operationIndex] using hv
    · simp [transfers,hi,hb] at h
  | some i =>
    have hc' : (i < 15 ∧ branchCheck spec.edge i before no false = true) ∧
        branchCheck spec.edge i before yes true = true := by
      simpa only [transfers,hi,Bool.and_eq_true_iff,decide_eq_true_eq] using h
    have hc : i < 15 ∧ branchCheck spec.edge i before no false = true ∧
        branchCheck spec.edge i before yes true = true := ⟨hc'.1.1,hc'.1.2,hc'.2⟩
    have htarget := hbank i hc.1
    cases hb : operationBranch spec.edge (bank i) with
    | false =>
      have hs := branchCheck_sound spec.edge i before no false hc.2.1 (bank i) htarget hb
      intro j hj
      by_cases hj' : j = i
      · subst j
        simpa [operandValue,updateBank,hi,hb] using hs.1
      · have hv := hs.2 j hj hj' (bank j) (hbank j hj)
        simpa [operandValue,updateBank,hi,hb,hj'] using hv
    | true =>
      have hs := branchCheck_sound spec.edge i before yes true hc.2.2 (bank i) htarget hb
      intro j hj
      by_cases hj' : j = i
      · subst j
        simpa [operandValue,updateBank,hi,hb] using hs.1
      · have hv := hs.2 j hj hj' (bank j) (hbank j hj)
        simpa [operandValue,updateBank,hi,hb,hj'] using hv

end Shared.PNP.Record285.GrammarCoreZero
