import PASoundness.PAtoCompactQuantifiedRefutation
import PASoundness.CompactFreshen

/-! Syntactic freshness of the generated filter selector in the named base,
step, and classification formulas. These are finite-name bounds, not K proof
data or an induction proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionSelectorAuxiliary
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor

/-- If a name is absent from a predicate and distinct from the old and new
replacement labels, it is absent from the replaced predicate. -/
theorem replace_fresh (C t y : Nat) (f : Formula)
    (hC : C ∉ f.names) (ht : C ≠ t) (hy : C ≠ y) :
    C ∉ (replace t y f).names := by
  intro h
  exact hC ((replace_names_outside t y C f ht hy).mp h)

/-- Any name above the displayed auxiliary names and outside f is fresh for
all three named schemas used by candidate induction. -/
theorem auxiliary_schemas_fresh (C Y t v m z w p q : Nat) (f : Formula)
    (hC : C ∉ f.names) (hY : Y < C) (ht : t < C) (hv : v < C)
    (hm : m < C) (hz : z < C) (hw : w < C) (hp : p < C) (hq : q < C) :
    C ∉ (namedAllBase t m z f).names ∧
    C ∉ (namedAllSteps Y t v m w p q f).names ∧
    C ∉ (namedAllClassification Y v m z w p q).names := by
  have hvf := replace_fresh C t v f hC (by omega) (by omega)
  have hmf := replace_fresh C t m f hC (by omega) (by omega)
  have hnY : C ≠ Y := by omega
  have hnt : C ≠ t := by omega
  have hnv : C ≠ v := by omega
  have hnm : C ≠ m := by omega
  have hnz : C ≠ z := by omega
  have hnw : C ≠ w := by omega
  have hnp : C ≠ p := by omega
  have hnq : C ≠ q := by omega
  constructor
  · simp [namedAllBase, namedUniformBaseBody, Formula.names, hnm, hnz, hmf]
  constructor
  · simp [namedAllSteps, namedUniformStepBody, namedPredecessorCore, namedBoth,
      namedSuccessorBody, namedEither, transitiveBody, Formula.names,
      hnm, hnv, hnY, hnw, hnp, hnq, hvf, hmf]
  · simp [namedAllClassification, namedPredecessorCore, namedBoth,
      namedSuccessorBody, namedEither, transitiveBody, Formula.names,
      hnm, hnv, hnY, hnz, hnw, hnp, hnq]

/-- Specialized to the actual filter selector. Only the six remaining
auxiliary labels need numerical bounds; the selector already exceeds Y,t. -/
theorem selector_schemas_fresh (Y t v m z w p q : Nat) (f : Formula)
    (hC : filterPredicate Y t (neg f.encode) ∉ f.names)
    (haux : ∀ a ∈ [v,m,z,w,p,q], a < filterPredicate Y t (neg f.encode)) :
    filterPredicate Y t (neg f.encode) ∉ (namedAllBase t m z f).names ∧
    filterPredicate Y t (neg f.encode) ∉ (namedAllSteps Y t v m w p q f).names ∧
    filterPredicate Y t (neg f.encode) ∉ (namedAllClassification Y v m z w p q).names := by
  have hc := filterPredicate_bounds Y t (neg f.encode)
  exact auxiliary_schemas_fresh _ Y t v m z w p q f hC hc.1 hc.2.1
    (haux v (by simp)) (haux m (by simp)) (haux z (by simp))
    (haux w (by simp)) (haux p (by simp)) (haux q (by simp))

/-- In particular, it suffices to choose every auxiliary at most Y. -/
theorem selector_schemas_fresh_of_aux_le (Y t v m z w p q : Nat) (f : Formula)
    (hC : filterPredicate Y t (neg f.encode) ∉ f.names)
    (haux : ∀ a ∈ [v,m,z,w,p,q], a ≤ Y) :
    filterPredicate Y t (neg f.encode) ∉ (namedAllBase t m z f).names ∧
    filterPredicate Y t (neg f.encode) ∉ (namedAllSteps Y t v m w p q f).names ∧
    filterPredicate Y t (neg f.encode) ∉ (namedAllClassification Y v m z w p q).names := by
  apply selector_schemas_fresh Y t v m z w p q f hC
  intro a ha
  have hY := (filterPredicate_bounds Y t (neg f.encode)).1
  have := haux a ha
  omega

end PASoundness.PAtoCompactInductionSelectorAuxiliary

#print axioms PASoundness.PAtoCompactInductionSelectorAuxiliary.replace_fresh
#print axioms PASoundness.PAtoCompactInductionSelectorAuxiliary.auxiliary_schemas_fresh
#print axioms PASoundness.PAtoCompactInductionSelectorAuxiliary.selector_schemas_fresh

#print axioms PASoundness.PAtoCompactInductionSelectorAuxiliary.selector_schemas_fresh_of_aux_le
