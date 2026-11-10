import PASoundness.PAtoCompactAdditionOldTargetUniform

/-! A clean old graph supplies the uniform source guard required by the
old-target uniqueness proof for the addition-successor extension. The clean
graph remains an explicit antecedent; no graph existence, full bijection,
arithmetic totality, or semantic soundness is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetSourceGuard
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdditionSuccessorGraphClean PASoundness.PAtoCompactAdditionOldTargetUniform
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For every edge at old target 28, cleanliness supplies old source-domain
membership. The displayed graph and endpoint labels are literal. -/
def source_guard_from_clean : KDerivation (imp oldClean.encode sourceGuardUniform.encode) := by
  let C := oldClean.encode
  let F : Formula := .imp (graphFormula 6 29 28) (.member 31 29)
  have hp : KDerivation (imp C F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(graphFormula 6 29 28).encode,C]
    have hg : Context Γ (graphFormula 6 29 28).encode := Context.head _ _
    have hc : Context Γ C := .hypothesis (by simp [Γ])
    exact Context.conjunctionLeft (.mp hg (.mp hc (.closed (clean_endpoints 29 28 (by decide)))))
  have hv : KDerivation (imp C (allCode 29 C)) := oldClean.vacuity 29 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hc : Context [C] C := Context.head [] _
  have hf : Context [C] F.encode := .mp hc (.closed hp)
  exact Context.generalize 29 (by
    intro z hz
    have he : z = C := by simpa using hz
    subst z
    exact hv) hf

theorem source_guard_from_clean_certificate :
    theoremCode (certificate source_guard_from_clean) =
      imp oldClean.encode sourceGuardUniform.encode := certificate_correct source_guard_from_clean
end PASoundness.PAtoCompactAdditionOldTargetSourceGuard
#print axioms PASoundness.PAtoCompactAdditionOldTargetSourceGuard.source_guard_from_clean
#print axioms PASoundness.PAtoCompactAdditionOldTargetSourceGuard.source_guard_from_clean_certificate
