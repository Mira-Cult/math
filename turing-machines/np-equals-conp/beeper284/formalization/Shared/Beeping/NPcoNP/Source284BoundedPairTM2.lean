import Shared.ComplexityBridge.TM2BoundedUnary
import Shared.ComplexityBridge.TM2UnaryProductLength
import Shared.ComplexityBridge.CNFBinaryPairAdd
import Shared.ComplexityBridge.TM2If
import Mathlib.Data.Nat.Pairing

/-! A bounded implementation of the natural pairing used by the countdown
control. Both binary components are clamped to an explicitly supplied unary
budget. Squaring uses the charged unary product machine; this file does not
claim polynomial-time unbounded binary multiplication, unpairing, table
serialization, or correctness of the physical machine. -/
namespace Shared.Beeping.NPcoNP.Source284BoundedPairTM2

open Shared.ComplexityBridge

abbrev Input := List Bool × (Nat × Nat)

def leftTokens (p : Input) : List Bool := TM2BoundedUnary.expand (p.1, p.2.1)
def rightTokens (p : Input) : List Bool := TM2BoundedUnary.expand (p.1, p.2.2)

def pairBounded (p : Input) : Nat :=
  let a := leftTokens p
  let b := rightTokens p
  if TM2BoundedWitnessGuard.guard (b,a.length) then
    TM2UnaryProductLength.product (b,b) + a.length
  else
    TM2UnaryProductLength.product (a,a) + a.length + b.length

theorem guard_decide (tokens : List Bool) (n : Nat) :
    TM2BoundedWitnessGuard.guard (tokens,n) = decide (n < tokens.length) := by
  apply Bool.eq_iff_iff.mpr
  simp [TM2BoundedWitnessGuard.guard_correct]

/-- Even when one or both inputs exceed the budget, the computed value is
precisely pairing of the two clipped components. -/
theorem pairBounded_clamped (budget : List Bool) (a b : Nat) :
    pairBounded (budget,(a,b)) = Nat.pair (min a budget.length) (min b budget.length) := by
  simp [pairBounded, leftTokens, rightTokens, guard_decide,
    TM2BoundedUnary.expand_correct, TM2UnaryProductLength.product_correct, Nat.pair]

/-- Under the explicit unary-budget hypotheses the original pair is
computed exactly. -/
theorem pairBounded_correct (budget : List Bool) (a b : Nat)
    (ha : a ≤ budget.length) (hb : b ≤ budget.length) :
    pairBounded (budget,(a,b)) = Nat.pair a b := by
  simpa [Nat.min_eq_left ha, Nat.min_eq_left hb] using pairBounded_clamped budget a b

private theorem inputFirst : ComplexityTheory.IsPolyTime (fun p : Input => p.1) :=
  TM2PairFirst.first_isPolyTime

private theorem inputPair : ComplexityTheory.IsPolyTime (fun p : Input => p.2) :=
  TM2GuardAllStep.second_isPolyTime

private theorem inputA : ComplexityTheory.IsPolyTime (fun p : Input => p.2.1) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun p : Nat × Nat => p.1)
    inputPair TM2PairFirst.first_isPolyTime

private theorem inputB : ComplexityTheory.IsPolyTime (fun p : Input => p.2.2) :=
  TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun p : Nat × Nat => p.2)
    inputPair TM2GuardAllStep.second_isPolyTime

theorem leftTokens_isPolyTime : ComplexityTheory.IsPolyTime leftTokens := by
  exact TM2Compose.isPolyTime_comp (fun p : Input => (p.1,p.2.1)) TM2BoundedUnary.expand
    (TM2GuardAllStep.pair_isPolyTime _ _ inputFirst inputA) TM2BoundedUnary.expand_isPolyTime

theorem rightTokens_isPolyTime : ComplexityTheory.IsPolyTime rightTokens := by
  exact TM2Compose.isPolyTime_comp (fun p : Input => (p.1,p.2.2)) TM2BoundedUnary.expand
    (TM2GuardAllStep.pair_isPolyTime _ _ inputFirst inputB) TM2BoundedUnary.expand_isPolyTime

private theorem add_isPolyTime {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) (hg : ComplexityTheory.IsPolyTime g) :
    ComplexityTheory.IsPolyTime (fun x => f x + g x) := by
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime
  simpa [CNFBinaryPairAdd.addPair] using h

/-- All expansion, comparison, products, and output construction are charged
in the full canonical encoding of the input, including its unary budget. -/
theorem pairBounded_isPolyTime : ComplexityTheory.IsPolyTime pairBounded := by
  let a : Input → List Bool := leftTokens
  let b : Input → List Bool := rightTokens
  let al : Input → Nat := fun p => (a p).length
  let bl : Input → Nat := fun p => (b p).length
  let aa : Input → Nat := fun p => TM2UnaryProductLength.product (a p,a p)
  let bb : Input → Nat := fun p => TM2UnaryProductLength.product (b p,b p)
  let flag : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (b p,al p)
  let yes : Input → Nat := fun p => bb p + al p
  let no : Input → Nat := fun p => aa p + al p + bl p
  have ha : ComplexityTheory.IsPolyTime a := leftTokens_isPolyTime
  have hb : ComplexityTheory.IsPolyTime b := rightTokens_isPolyTime
  have hal : ComplexityTheory.IsPolyTime al := TM2Compose.isPolyTime_comp a List.length ha TM2BinaryListLength.length_isPolyTime
  have hbl : ComplexityTheory.IsPolyTime bl := TM2Compose.isPolyTime_comp b List.length hb TM2BinaryListLength.length_isPolyTime
  have haa : ComplexityTheory.IsPolyTime aa := TM2Compose.isPolyTime_comp (fun p => (a p,a p)) TM2UnaryProductLength.product
    (TM2GuardAllStep.pair_isPolyTime a a ha ha) TM2UnaryProductLength.product_isPolyTime
  have hbb : ComplexityTheory.IsPolyTime bb := TM2Compose.isPolyTime_comp (fun p => (b p,b p)) TM2UnaryProductLength.product
    (TM2GuardAllStep.pair_isPolyTime b b hb hb) TM2UnaryProductLength.product_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp (fun p => (b p,al p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime b al hb hal) TM2BoundedWitnessGuard.guard_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := add_isPolyTime bb al hbb hal
  have hn : ComplexityTheory.IsPolyTime no := add_isPolyTime (fun p => aa p + al p) bl (add_isPolyTime aa al haa hal) hbl
  exact TM2If.if_isPolyTime flag yes no hf hy hn

end Shared.Beeping.NPcoNP.Source284BoundedPairTM2
