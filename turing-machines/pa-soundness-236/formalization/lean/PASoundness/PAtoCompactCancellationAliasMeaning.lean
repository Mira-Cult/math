import PASoundness.PAtoCompactEquivalentEndpointAlias
import PASoundness.PAtoCompactOrdinalEquivalence

/-! Standard-HF calibration of the cancellation endpoint's guarded alias.
This is a semantic check only: it neither derives a K theorem nor assumes
K soundness, quotient laws, or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCancellationAliasMeaning
open PASoundness.CompactNamed PASoundness.CompactMatrix
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalEquivalence
open PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactRestrictedEquivalentTarget
open PASoundness.HFCoding

/-- Assignment for the canonical equality formula: its free endpoints 0,1
receive the original values of displayed endpoints 2,5. -/
def endpointAssignment (ρ : Environment) : Environment :=
  update (update ρ 0 (ρ 2)) 1 (ρ 5)

private def andFormula (a b : CompactNamed.Formula) : CompactNamed.Formula :=
  (a.imp b.not).not

/-- The equality guards bind aliases 40 and 41 to endpoints 2 and 5. This
holds for every assignment, including equal endpoint values. -/
theorem guarded_realize (f : CompactNamed.Formula) (ρ : Environment) :
    (guarded f).Realize ρ ↔
      f.Realize (update (update ρ 40 (ρ 2)) 41 (ρ 5)) := by
  classical
  change (CompactNamed.Formula.ex 40 (andFormula (.equal 40 2)
    (.ex 41 (andFormula (.equal 41 5) f)))).Realize ρ ↔ _
  simp [andFormula, CompactNamed.Formula.Realize, CompactNamed.Formula.not, update]

private theorem original_fresh : 40 ∉ equivalentFormula.names ∧ 41 ∉ equivalentFormula.names := by decide
private theorem prepared_fresh : 40 ∉ preparedEquivalent.names ∧ 41 ∉ preparedEquivalent.names := by decide

/-- The guarded original formula has exactly the standard-HF truth value of
the canonical equality formula with its endpoints assigned from 2 and 5. -/
theorem guarded_original_realize (ρ : Environment) :
    (guarded originalAliases).Realize ρ ↔ equivalentFormula.Realize (endpointAssignment ρ) := by
  rw [guarded_realize]
  unfold originalAliases
  rw [replace_realize 1 41 (replace 0 40 equivalentFormula) (by decide) (by decide)]
  rw [replace_realize 0 40 equivalentFormula (by decide) (by decide)]
  apply Formula.realize_agree
  intro v hv
  have hv40 : v ≠ 40 := fun h => original_fresh.1 (h ▸ hv)
  have hv41 : v ≠ 41 := fun h => original_fresh.2 (h ▸ hv)
  by_cases h0 : v = 0 <;> by_cases h1 : v = 1 <;>
    simp [endpointAssignment, update, h0, h1, hv40, hv41]

/-- The prepared, alpha-renamed formula has the same guarded reading. -/
theorem guarded_prepared_realize (ρ : Environment) :
    (guarded preparedAliases).Realize ρ ↔ preparedEquivalent.Realize (endpointAssignment ρ) := by
  rw [guarded_realize]
  unfold preparedAliases
  rw [replace_realize 1 41 (replace 0 40 preparedEquivalent) (by decide) (by decide)]
  rw [replace_realize 0 40 preparedEquivalent (by decide) (by decide)]
  apply Formula.realize_agree
  intro v hv
  have hv40 : v ≠ 40 := fun h => prepared_fresh.1 (h ▸ hv)
  have hv41 : v ≠ 41 := fun h => prepared_fresh.2 (h ▸ hv)
  by_cases h0 : v = 0 <;> by_cases h1 : v = 1 <;>
    simp [endpointAssignment, update, h0, h1, hv40, hv41]

/-- The alpha-prepared endpoint target has the same standard-HF truth value
as the canonical formula with free endpoints assigned from 2 and 5. -/
theorem endpoint_target_realize (ρ : Environment) :
    endpointTarget.Realize ρ ↔ equivalentFormula.Realize (endpointAssignment ρ) := by
  unfold endpointTarget
  rw [replace_realize 1 5 (replace 0 2 preparedEquivalent) (by decide) (by decide)]
  rw [replace_realize 0 2 preparedEquivalent (by decide) (by decide)]
  have he : preparedEquivalent.Realize
      (update (update ρ 1 (ρ 5)) 0 ((update ρ 1 (ρ 5)) 2)) ↔
      preparedEquivalent.Realize (endpointAssignment ρ) := by
    apply Formula.realize_agree
    intro v hv
    by_cases h0 : v = 0 <;> by_cases h1 : v = 1 <;>
      simp [endpointAssignment, update, h0, h1]
  exact he.trans (prepare_equivalent.semantic (endpointAssignment ρ)).symm

/-- Standard-HF equality of the guarded alias and prepared endpoint target,
proved directly from the named semantic transformations rather than K
derivation soundness. -/
theorem guarded_iff_endpoint (ρ : Environment) :
    (guarded originalAliases).Realize ρ ↔ endpointTarget.Realize ρ :=
  (guarded_original_realize ρ).trans (endpoint_target_realize ρ).symm

/-- On standard finite ordinal endpoints, the guarded alias means equality
of their indices. This is a calibration of the displayed formula only. -/
theorem guarded_ordinal_iff (ρ : Environment) (n m : Nat)
    (h2 : ρ 2 = (ordinal n).code) (h5 : ρ 5 = (ordinal m).code) :
    (guarded originalAliases).Realize ρ ↔ n = m := by
  rw [guarded_original_realize]
  have h0 : endpointAssignment ρ 0 = (ordinal n).code := by simpa [endpointAssignment, update] using h2
  have h1 : endpointAssignment ρ 1 = (ordinal m).code := by simpa [endpointAssignment, update] using h5
  rw [← Formula.encode_realize]
  exact standard_ordinal_iff (endpointAssignment ρ) n m h0 h1

/-- Numeric encodings have the same reading in standard HF. In particular,
their literal code 1 is self-membership, false under every HF assignment;
this statement is not applied to arbitrary raw K models. -/
theorem guarded_encoded_ordinal_iff (ρ : Environment) (n m : Nat)
    (h2 : ρ 2 = (ordinal n).code) (h5 : ρ 5 = (ordinal m).code) :
    (decode (guarded originalAliases).encode).Realize ρ ↔ n = m := by
  rw [Formula.encode_realize]
  exact guarded_ordinal_iff ρ n m h2 h5

end PASoundness.PAtoCompactCancellationAliasMeaning

#print axioms PASoundness.PAtoCompactCancellationAliasMeaning.guarded_original_realize
#print axioms PASoundness.PAtoCompactCancellationAliasMeaning.endpoint_target_realize
#print axioms PASoundness.PAtoCompactCancellationAliasMeaning.guarded_ordinal_iff
#print axioms PASoundness.PAtoCompactCancellationAliasMeaning.guarded_encoded_ordinal_iff
