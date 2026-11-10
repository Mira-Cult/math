import PASoundness.PAtoCompactAdditionEliminateCleanOldGraph
import PASoundness.PAtoCompactAdditionSuccessorPackage
import PASoundness.PAtoCompactAdditionCandidateCutStep
import PASoundness.PAtoCompactAdditionDomainTransitivity

/-! K successor step for one explicit old addition cut and suffix. Candidate
and raw-successor assumptions are literal object-level antecedents. This is
not a global induction or addition totality theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorLocalStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactAdditionRightContext PASoundness.PAtoCompactAdditionSuccessorEquivStep
open PASoundness.PAtoCompactAdditionEliminateCleanOldGraph PASoundness.PAtoCompactAdditionSuccessorPackage
open PASoundness.PAtoCompactAdditionCandidateCutStep PASoundness.PAtoCompactAdditionDomainTransitivity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def fixedAssumptions : Formula := namedBoth (domainAt 100 31) (namedBoth (domainAt 100 32)
  (namedBoth (namedSuccessor 31 38 39) (namedSuccessor 32 45 39)))
def oldCut : Formula := namedEither (.equal 33 32) (.member 32 33)
def oldLeftEquiv : Formula := equivAt 30 33
def oldFilter : Formula := suffixF
def oldRightEquiv : Formula := equivAt 31 34

/-- A literal old cut and suffix yield the new addition relation when their
source and result have the displayed candidate guards and successors. -/
def local_step : KDerivation (imp fixedAssumptions.encode
    (imp oldCut.encode (imp oldLeftEquiv.encode (imp oldFilter.encode
      (imp oldRightEquiv.encode addition45.encode))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldRightEquiv.encode,oldFilter.encode,oldLeftEquiv.encode,oldCut.encode,fixedAssumptions.encode]
  have he : Context Γ oldRightEquiv.encode := .head _ _
  have hf : Context Γ oldFilter.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ oldLeftEquiv.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ oldCut.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ fixedAssumptions.encode := .hypothesis (by simp [Γ])
  have hD1 : Context Γ (domainAt 100 31).encode := Context.conjunctionLeft hp
  have hr := Context.conjunctionRight hp
  have hD2 : Context Γ (domainAt 100 32).encode := Context.conjunctionLeft hr
  have hs : Context Γ (successorCode 31 38 39) := Context.conjunctionLeft (Context.conjunctionRight hr)
  have ht : Context Γ (successorCode 32 45 39) := Context.conjunctionRight (Context.conjunctionRight hr)
  have hcut : Context Γ (both (neg (member 33 32)) (member 45 33)) :=
    .mp ht (.mp hc (.mp hD2 (.closed candidate_cut_step)))
  have houtside := Context.conjunctionLeft hcut
  have hcutNew := Context.conjunctionRight hcut
  have hsrc : Context Γ (transitiveCode 31 37 38) := .mp hD1 (.closed source_transitive)
  have hresult : Context Γ (transitiveCode 32 37 38) := .mp hD2 (.closed result_transitive)
  have hgraphFree : Context Γ graphFreeAssumptions.encode := by
    exact Context.conjunctionIntro hf (Context.conjunctionIntro hs (Context.conjunctionIntro hsrc hresult))
  have hex : Context Γ suffixAndEquiv.encode :=
    .mp ht (.mp houtside (.mp hgraphFree (.mp he (.closed eliminate_old_graph))))
  have hlocal : Context Γ (imp (namedBoth suffixWitness (equivAt 38 40)).encode addition45.encode) := by
    apply Context.deduction
    let Δ := (namedBoth suffixWitness (equivAt 38 40)).encode :: Γ
    have hw : Context Δ (namedBoth suffixWitness (equivAt 38 40)).encode := .head _ _
    have hw1 := Context.conjunctionLeft hw
    have heq := Context.conjunctionRight hw
    have hnewFilter := Context.conjunctionRight hw1
    exact .mp heq (.mp hnewFilter (.mp (.under hl _) (.mp (.under hcutNew _)
      (.closed addition_from_cut_suffix))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 40 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h1 : h = oldRightEquiv.encode
    · subst h; exact oldRightEquiv.vacuity 40 (by decide)
    by_cases h2 : h = oldFilter.encode
    · subst h; exact oldFilter.vacuity 40 (by decide)
    by_cases h3 : h = oldLeftEquiv.encode
    · subst h; exact oldLeftEquiv.vacuity 40 (by decide)
    by_cases h4 : h = oldCut.encode
    · subst h; exact oldCut.vacuity 40 (by decide)
    have h5 : h = fixedAssumptions.encode := by simpa [h1,h2,h3,h4] using hh
    subst h
    exact fixedAssumptions.vacuity 40 (by decide)
  have hall := Context.generalize 40 hv hlocal
  exact Context.existsElim (addition45.vacuity 40 (by decide)) hall hex

theorem local_step_certificate : theoremCode (certificate local_step) =
    imp fixedAssumptions.encode (imp oldCut.encode (imp oldLeftEquiv.encode
      (imp oldFilter.encode (imp oldRightEquiv.encode addition45.encode)))) :=
  certificate_correct local_step
end PASoundness.PAtoCompactAdditionSuccessorLocalStep
#print axioms PASoundness.PAtoCompactAdditionSuccessorLocalStep.local_step
#print axioms PASoundness.PAtoCompactAdditionSuccessorLocalStep.local_step_certificate
