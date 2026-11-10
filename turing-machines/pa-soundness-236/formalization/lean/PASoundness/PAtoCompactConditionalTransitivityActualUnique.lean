import PASoundness.PAtoCompactConditionalTransitivityFirstUnique
import PASoundness.PAtoCompactConditionalTransitivityFirstInverse
import PASoundness.PAtoCompactConditionalTransitivitySecondUnique

/-! The actual two supplied bijection clauses imply pointwise uniqueness of
two guarded compositional paths. The graph is not constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityActualUnique
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityUniqueness
open PASoundness.PAtoCompactConditionalTransitivityFirstUnique
open PASoundness.PAtoCompactConditionalTransitivityFirstInverse
open PASoundness.PAtoCompactConditionalTransitivitySecondUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under the literal two bijection clauses and their displayed domain guards,
two supplied paths from the same source have equal target values. -/
def target_unique : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode (imp (member 0 2)
      (imp firstPath (imp secondPath (equal 3 5)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondPath,firstPath,member 0 2,secondBijection.encode,bijectionFormula.encode]
  have hq : Context Γ secondPath := Context.head _ _
  have hp : Context Γ firstPath := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 0 2) := .hypothesis (by simp [Γ])
  have hg : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 10) := Context.conjunctionLeft hp
  have hfu : Context Γ firstUnique := .mp ha (.mp hf (.closed first_unique_of_bijection))
  have hgu : Context Γ secondUnique := .mp hb (.mp hg (.closed second_unique_of_bijection))
  exact .mp hq (.mp hp (.mp ha (.mp hgu (.mp hfu (.closed path_target_unique)))))

/-- Dually, two supplied paths to the same target have equal source values. -/
def source_unique : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode (imp (member 8 3)
      (imp firstPreimagePath (imp secondPreimagePath (equal 2 4)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [secondPreimagePath,firstPreimagePath,member 8 3,
    secondBijection.encode,bijectionFormula.encode]
  have hq : Context Γ secondPreimagePath := Context.head _ _
  have hp : Context Γ firstPreimagePath := .hypothesis (by simp [Γ])
  have hc : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hg : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 10) := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hfu : Context Γ firstInverseUnique :=
    .mp hb (.mp hf (.closed first_inverse_unique_of_bijection))
  have hgu : Context Γ secondInverseUnique :=
    .mp hc (.mp hg (.closed second_inverse_unique_of_bijection))
  exact .mp hq (.mp hp (.mp hc (.mp hfu (.mp hgu (.closed path_source_unique)))))

theorem target_unique_certificate : theoremCode (certificate target_unique) =
    imp bijectionFormula.encode (imp secondBijection.encode (imp (member 0 2)
      (imp firstPath (imp secondPath (equal 3 5))))) := certificate_correct target_unique

theorem source_unique_certificate : theoremCode (certificate source_unique) =
    imp bijectionFormula.encode (imp secondBijection.encode (imp (member 8 3)
      (imp firstPreimagePath (imp secondPreimagePath (equal 2 4))))) := certificate_correct source_unique

end PASoundness.PAtoCompactConditionalTransitivityActualUnique

#print axioms PASoundness.PAtoCompactConditionalTransitivityActualUnique.target_unique
#print axioms PASoundness.PAtoCompactConditionalTransitivityActualUnique.source_unique
#print axioms PASoundness.PAtoCompactConditionalTransitivityActualUnique.target_unique_certificate
#print axioms PASoundness.PAtoCompactConditionalTransitivityActualUnique.source_unique_certificate
