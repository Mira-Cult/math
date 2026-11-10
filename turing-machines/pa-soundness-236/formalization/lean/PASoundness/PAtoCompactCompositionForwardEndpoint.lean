import PASoundness.PAtoCompactPartialCompositionOutputUnique

/-! New-endpoint forward coverage of a supplied composition graph. Image
uniqueness, membership guards, endpoint equality, both queried path edges and
the selected graph edge remain explicit K antecedents. This constructs no
graph or witness and makes no induction or quotient claim. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionForwardEndpoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialCompositionOutputUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A guarded path from queried source 2, equal to endpoint 10, has the same
output as the two supplied unique image witnesses. An existing selected
composite edge can therefore be transported to queried coordinates. -/
def endpoint_coverage : KDerivation
    (imp firstUnique.encode (imp secondUnique.encode (imp (equal 2 10)
      (imp (member 1 4) (imp (graphFormula 6 2 4).encode
        (imp (member 8 3) (imp (graphFormula 7 4 3).encode
          (imp (graphFormula 17 10 12).encode (graphFormula 17 2 3).encode)))))))) := by
  have hsrc := (equalityReplace 10 2 (graphFormula 17 10 12) (by decide) (by decide)).1
  have hsrc' : replace 10 2 (graphFormula 17 10 12) = graphFormula 17 2 12 := by decide
  rw [hsrc'] at hsrc
  have htarget := (equalityReplace 12 3 (graphFormula 17 2 12) (by decide) (by decide)).1
  have htarget' : replace 12 3 (graphFormula 17 2 12) = graphFormula 17 2 3 := by decide
  rw [htarget'] at htarget
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 17 10 12).encode, (graphFormula 7 4 3).encode,
    member 8 3, (graphFormula 6 2 4).encode, member 1 4, equal 2 10,
    secondUnique.encode, firstUnique.encode]
  have hedge : Context Γ (graphFormula 17 10 12).encode := Context.head _ _
  have hg2 : Context Γ (graphFormula 7 4 3).encode := .hypothesis (by simp [Γ])
  have hc : Context Γ (member 8 3) := .hypothesis (by simp [Γ])
  have hg1 : Context Γ (graphFormula 6 2 4).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (member 1 4) := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 2 10) := .hypothesis (by simp [Γ])
  have hu2 : Context Γ secondUnique.encode := .hypothesis (by simp [Γ])
  have hu1 : Context Γ firstUnique.encode := .hypothesis (by simp [Γ])
  have hout : Context Γ (equal 3 12) :=
    .mp hg2 (.mp hc (.mp hg1 (.mp hb (.mp he (.mp hu2 (.mp hu1 (.closed selected_output_unique)))))))
  have hedge' : Context Γ (graphFormula 17 2 12).encode :=
    .mp hedge (.mp (Context.eqSymm he) (.closed hsrc))
  exact .mp hedge' (.mp (Context.eqSymm hout) (.closed htarget))

theorem endpoint_coverage_certificate :
    theoremCode (certificate endpoint_coverage) =
      imp firstUnique.encode (imp secondUnique.encode (imp (equal 2 10)
        (imp (member 1 4) (imp (graphFormula 6 2 4).encode
          (imp (member 8 3) (imp (graphFormula 7 4 3).encode
            (imp (graphFormula 17 10 12).encode (graphFormula 17 2 3).encode))))))) :=
  certificate_correct endpoint_coverage

end PASoundness.PAtoCompactCompositionForwardEndpoint

#print axioms PASoundness.PAtoCompactCompositionForwardEndpoint.endpoint_coverage
#print axioms PASoundness.PAtoCompactCompositionForwardEndpoint.endpoint_coverage_certificate
