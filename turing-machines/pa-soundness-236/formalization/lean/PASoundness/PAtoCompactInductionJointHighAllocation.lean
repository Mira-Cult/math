import PASoundness.PAtoCompactInductionJointLowAllocation
import PASoundness.PAtoCompactInductionAugmentedGuard
import PASoundness.PAtoCompactFilteredSubset
import PASoundness.PAtoCompactAdjunction

/-! Source-dependent high allocation and selector bounds for the shared
induction interfaces. This is syntactic name arithmetic only; engine selector
membership and formula-specific name clauses are separate obligations. -/
namespace PASoundness.PAtoCompactInductionJointHighAllocation
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactGuardedAllImp PASoundness.PAtoCompactGuardedAllImpAlignment
open PASoundness.PAtoCompactDirectGeneralization PASoundness.PAtoCompactInductionAugmentedGuard
open PASoundness.PAtoCompactInductionJointLowAllocation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactAdjunction

/-- Place the zero-graph allocator after the translated predicate and all low
names. -/
def highBase (φ : Peano.Formula) (x : Nat) : Nat :=
  let N := lowBound φ x
  let m := N+100
  let t := instanceBinder φ x m
  max ((scopeAt φ x t).names.sup id)
    (max (N+101) (guardBase (Peano.inductionAxiom φ x))) + 1

/-- The graph base is independently chosen above the augmented source guard. -/
def graphBase (φ : Peano.Formula) (x : Nat) : Nat :=
  max (highBase φ x) (guardBase (augmented (Peano.inductionAxiom φ x) (lowBound φ x+1))) + 1

/-- High names exceed the constructed scoped predicate, low names and guard;
the filter selector exceeds the container name, and the adjunction selector
exceeds both the container and its chosen witness. -/
theorem high_allocation (φ : Peano.Formula) (x : Nat) :
    let N := lowBound φ x
    let m := N+100
    let t := instanceBinder φ x m
    let f := scopeAt φ x t
    let B := highBase φ x
    let Y := B+100
    let point := B+101
    let gb := graphBase φ x
    N+101 < B ∧ f.names.sup id < B ∧ guardBase (Peano.inductionAxiom φ x) ≤ B ∧
    m < B ∧ Y ∉ f.names ∧ Y ∉ (Peano.inductionAxiom φ x).freeVarFinset ∧
    N+1 < gb ∧ m < gb ∧ guardBase (augmented (Peano.inductionAxiom φ x) (N+1)) ≤ gb ∧
    Y < filterPredicate Y t (neg f.encode) ∧
    B+5 ≠ adjunctionPredicate (N+2) point ∧ Y ≠ adjunctionPredicate (N+2) point := by
  dsimp only
  let N := lowBound φ x
  let m := N+100
  let t := instanceBinder φ x m
  let f := scopeAt φ x t
  let B := highBase φ x
  let Y := B+100
  let point := B+101
  let gb := graphBase φ x
  have hb1 : f.names.sup id < B := by
    dsimp [B, highBase, f, N, m, t]
    have hh := Nat.le_max_left ((scopeAt φ x (instanceBinder φ x (lowBound φ x + 100))).names.sup id)
      (max (lowBound φ x + 101) (guardBase (Peano.inductionAxiom φ x)))
    omega
  have hb2 : N+101 < B := by
    dsimp [B, highBase, N]
    have h1 := Nat.le_max_left (lowBound φ x + 101) (guardBase (Peano.inductionAxiom φ x))
    have h2 := Nat.le_max_right
      ((scopeAt φ x (instanceBinder φ x (lowBound φ x + 100))).names.sup id)
      (max (lowBound φ x + 101) (guardBase (Peano.inductionAxiom φ x)))
    omega
  have hb3 : guardBase (Peano.inductionAxiom φ x) ≤ B := by
    dsimp [B, highBase, N]
    have h1 := Nat.le_max_right (lowBound φ x + 101) (guardBase (Peano.inductionAxiom φ x))
    have h2 := Nat.le_max_right
      ((scopeAt φ x (instanceBinder φ x (lowBound φ x + 100))).names.sup id)
      (max (lowBound φ x + 101) (guardBase (Peano.inductionAxiom φ x)))
    omega
  have hsource : (Peano.inductionAxiom φ x).freeVarFinset.sup id < N := by
    dsimp [N, lowBound]
    have h1 := Nat.le_max_right ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id)
    have h2 := Nat.le_max_right (universalCeiling φ x)
      (max ((originalChild φ x).names.sup id) ((Peano.inductionAxiom φ x).freeVarFinset.sup id))
    omega
  have hfresh : Y ∉ f.names := by
    intro h
    have hh : Y ≤ f.names.sup id := Finset.le_sup (f := id) h
    dsimp [Y] at *
    omega
  have hfree : Y ∉ (Peano.inductionAxiom φ x).freeVarFinset := by
    intro h
    have hh : Y ≤ (Peano.inductionAxiom φ x).freeVarFinset.sup id := Finset.le_sup (f := id) h
    dsimp [Y] at *
    omega
  have hgb1 : B < gb := by
    dsimp [gb, graphBase, B, N]
    have hh := Nat.le_max_left (highBase φ x) (guardBase (augmented (Peano.inductionAxiom φ x) (lowBound φ x + 1)))
    omega
  have hgb2 : guardBase (augmented (Peano.inductionAxiom φ x) (N+1)) ≤ gb := by
    dsimp [gb, graphBase, N]
    have hh := Nat.le_max_right (highBase φ x) (guardBase (augmented (Peano.inductionAxiom φ x) (lowBound φ x + 1)))
    omega
  have hs := (filterPredicate_bounds Y t (neg f.encode)).1
  have ha := (predicate_names_lt (N+2) point).2
  dsimp only [N, m, t, f, B, Y, point, gb] at *
  exact ⟨hb2, hb1, hb3, by omega, hfresh, hfree, by omega, by omega, hgb2, hs, by omega, by omega⟩

end PASoundness.PAtoCompactInductionJointHighAllocation

#print axioms PASoundness.PAtoCompactInductionJointHighAllocation.high_allocation
