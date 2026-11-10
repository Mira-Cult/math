import PASoundness.PAtoCompactProductRowOutsidePrefix
import PASoundness.PAtoCompactFixedFirstCoverageBase

/-! K transport of the existential row coverage clause through a prefix
successor when the new point lies outside the row index. This does not
construct a row graph, require pair extensionality, or prove multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductRowOutsideCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactProductRowOutsidePrefix PASoundness.PAtoCompactFixedFirstCoverageBase
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def H : Formula := namedBoth (namedSuccessor 0 1 2) (Formula.member 31 0).not
private def C : Formula := .ex 4 (.ex 5 (namedBoth (graphFormula 6 3 4)
  (namedBoth (pairFormula 5 30 3) (graphFormula 7 5 4))))
private def I0 : Nat := both (member 0 3) (member 31 3)
private def I1 : Nat := both (member 1 3) (member 31 3)

private def coverage_point : KDerivation (imp H.encode
    (imp (imp I0 C.encode) (imp I1 C.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [H.encode]
  have hh : Context Γ H.encode := .head _ _
  have hpair : Context Γ (both (successorCode 0 1 2) (neg (member 31 0))) := by
    simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using hh
  have hs := Context.conjunctionLeft hpair
  have hn := Context.conjunctionRight hpair
  have heq := Context.mp hn (Context.mp hs (.closed outside_intersection_point))
  have hreverse : Context Γ (imp I1 I0) := Context.conjunctionLeft heq
  exact Context.implicationCongr hreverse (.closed (CompactHilbertBasis.identity C.encode))

/-- Coverage transfers from the old prefix to its successor when the added
point is outside the source domain, keeping the graph name 7 unchanged. -/
def outside_coverage : KDerivation (imp (successorCode 0 1 2)
    (imp (neg (member 31 0))
      (imp (coverage 7).encode (replace 0 1 (coverage 7)).encode))) := by
  have hv : KDerivation (imp H.encode (allCode 3 H.encode)) := H.vacuity 3 (by decide)
  have h := conditionalAllCongr 3 hv coverage_point
  have hold : (coverage 7).encode = allCode 3 (imp I0 C.encode) := by rfl
  have hnew : (replace 0 1 (coverage 7)).encode = allCode 3 (imp I1 C.encode) := by rfl
  rw [← hold, ← hnew] at h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 31 0),successorCode 0 1 2]
  have hn : Context Γ (neg (member 31 0)) := .head _ _
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  have hh : Context Γ H.encode := by
    simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using Context.conjunctionIntro hs hn
  exact .mp hh (.closed h)

theorem outside_coverage_certificate : theoremCode (certificate outside_coverage) =
    imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (imp (coverage 7).encode (replace 0 1 (coverage 7)).encode)) :=
  certificate_correct outside_coverage
end PASoundness.PAtoCompactProductRowOutsideCoverage
#print axioms PASoundness.PAtoCompactProductRowOutsideCoverage.outside_coverage
#print axioms PASoundness.PAtoCompactProductRowOutsideCoverage.outside_coverage_certificate
