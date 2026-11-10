import PASoundness.PAtoCompactPartialInverseCombine
import PASoundness.PAtoCompactPartialInverseBackwardAll

/-! The full partial-inverse successor invariant for supplied local witnesses.
Alias, image, inverse pair, point adjunction and successor graph are retained
as explicit premises. No witness elimination, induction or symmetry is
claimed in this module. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseSuppliedStep
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPartialInverseCoverageAll PASoundness.PAtoCompactPartialInverseCombine
open PASoundness.PAtoCompactPartialInverseBackwardAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- With all displayed local witnesses supplied, K derives the exact
prefix/graph-renamed successor partial-inverse invariant. -/
def supplied_step : KDerivation (imp suppliedPremises.encode newPartial.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suppliedPremises.encode]
  have hp : Context Γ suppliedPremises.encode := Context.head [] _
  have hb : Context Γ backwardCoverage.encode := .mp hp (.closed backward_all)
  exact .mp hb (.mp hp (.closed combine_successor_invariant))

theorem supplied_step_certificate : theoremCode (certificate supplied_step) =
    imp suppliedPremises.encode newPartial.encode := certificate_correct supplied_step

end PASoundness.PAtoCompactPartialInverseSuppliedStep

#print axioms PASoundness.PAtoCompactPartialInverseSuppliedStep.supplied_step
#print axioms PASoundness.PAtoCompactPartialInverseSuppliedStep.supplied_step_certificate
