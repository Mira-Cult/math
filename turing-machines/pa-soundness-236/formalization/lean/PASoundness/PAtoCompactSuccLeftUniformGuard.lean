import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactSuccLeftUniqueTransfer

/-! Uniform target-domain guard for old-source successor uniqueness. The
pointwise clean-edge implication is an explicit finite K proof-data premise;
this wrapper does not establish cleanliness or graph existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccLeftUniformGuard
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccLeftUniqueTransfer

/-- The literal cleanliness schema is vacuous in competitor name 4. Its bound
endpoint names and pair witnesses are retained exactly. -/
def clean_vacuity_four : KDerivation (imp cleanGraph (allCode 4 cleanGraph)) := by
  let f : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
  have hv := f.vacuity 4 (by decide)
  simpa [f, cleanGraph, Formula.encode] using hv

/-- A supplied pointwise clean-edge target proof lifts to all competitors. -/
def uniform_guard (hpoint : KDerivation (imp cleanGraph oldTargetGuard)) :
    KDerivation (imp cleanGraph (allCode 4 oldTargetGuard)) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hc : Context [cleanGraph] cleanGraph := Context.head [] cleanGraph
  have hp : Context [cleanGraph] oldTargetGuard := .mp hc (.closed hpoint)
  exact Context.generalize 4 (by
    intro h hh
    have he : h = cleanGraph := by simpa using hh
    subst h
    exact clean_vacuity_four) hp

theorem uniform_guard_certificate (hpoint : KDerivation (imp cleanGraph oldTargetGuard)) :
    theoremCode (certificate (uniform_guard hpoint)) =
      imp cleanGraph (allCode 4 oldTargetGuard) := certificate_correct (uniform_guard hpoint)

end PASoundness.PAtoCompactSuccLeftUniformGuard

#print axioms PASoundness.PAtoCompactSuccLeftUniformGuard.clean_vacuity_four
#print axioms PASoundness.PAtoCompactSuccLeftUniformGuard.uniform_guard
#print axioms PASoundness.PAtoCompactSuccLeftUniformGuard.uniform_guard_certificate
