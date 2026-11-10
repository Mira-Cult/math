import PASoundness.PAtoCompactMultiplicationTopPointAssembler
import PASoundness.PAtoCompactMultiplicationTopUniqueClosed
import PASoundness.PAtoCompactFreeVacuity

/-! Top-point forward coverage and target-guarded uniqueness for the
anchored multiplication successor graph. The graph, filter, old cleanliness,
suffix-map cleanliness and bijection are explicit K antecedents. This is
one point case, not the complete product matrix or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopForwardPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactMultiplicationCleanMapUnique41
open PASoundness.PAtoCompactMultiplicationTopCoverageWitness
open PASoundness.PAtoCompactMultiplicationTopCoverageTriple
open PASoundness.PAtoCompactMultiplicationTopPointAssembler
open PASoundness.PAtoCompactMultiplicationTopUniqueConditional
open PASoundness.PAtoCompactMultiplicationTopUniqueClosed
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- All graph and source conditions, independent of the chosen output 5. -/
def premises : Formula := namedBoth oldClean
  (namedBoth (replace 0 31 (noGarbage 64))
    (namedBoth witnessContext (namedBoth mapBijection40
      (namedBoth (.member 31 3) (replace 0 31 (coverage 64))))))

private def parts (h : Context Γ premises.encode) :
    Context Γ (both oldClean.encode (both (replace 0 31 (noGarbage 64)).encode
      (both witnessContext.encode (both mapBijection40.encode
        (both (member 31 3) (replace 0 31 (coverage 64)).encode))))) := by
  simpa [premises,namedBoth,Formula.not,Formula.encode,both,neg] using h

/-- Coverage under the displayed common hypotheses, retaining the actual
chosen map edge and triple for the later uniqueness proof. -/
private def coverage_from_premises : KDerivation
    (imp premises.encode (existsCode 5 tripleWitness.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [premises.encode]
  have h := parts (Context.head [] premises.encode)
  have hw : Context Γ witnessContext.encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight h))
  have hs : Context Γ (member 31 3) := Context.conjunctionLeft
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight h))))
  have hc : Context Γ (replace 0 31 (coverage 64)).encode := Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight h))))
  simpa [Formula.encode] using (.mp hs (.mp hc (.mp hw (.closed top_coverage_triple))) :
    Context Γ (Formula.ex 5 tripleWitness).encode)

/-- The retained selected map edge supplies the last hypothesis of the
independently constructed top-output uniqueness proof. -/
private def unique_from_witness : KDerivation
    (imp premises.encode (imp tripleWitness.encode topUnique.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [tripleWitness.encode,premises.encode]
  have hw : Context Γ tripleWitness.encode := .head _ _
  have hp : Context Γ premises.encode := .hypothesis (by simp [Γ])
  have h := parts hp
  have hw' : Context Γ (both (member 45 5)
      (both (graphFormula 6 3 5).encode
        PASoundness.PAtoCompactMultiplicationTopCoverageTriple.topTriple.encode)) := by
    simpa [tripleWitness,namedBoth,Formula.not,Formula.encode,both,neg] using hw
  have hwctx := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight h))
  have hwctx' : Context Γ (both suffixClean.encode suffixFilter.encode) := by
    simpa [witnessContext,namedBoth,Formula.not,Formula.encode,both,neg] using hwctx
  have ha : Context Γ assumptions.encode := by
    have hb := Context.conjunctionIntro (Context.conjunctionLeft h)
      (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight h))
        (Context.conjunctionIntro (Context.conjunctionLeft hwctx')
          (Context.conjunctionIntro
            (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight
              (Context.conjunctionRight h))))
            (Context.conjunctionIntro
              (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight
                (Context.conjunctionRight (Context.conjunctionRight h)))))
              (Context.conjunctionLeft (Context.conjunctionRight hw'))))))
    simpa [assumptions,namedBoth,Formula.not,Formula.encode,both,neg] using hb
  exact .mp ha (.closed top_unique)

/-- Under the displayed clean graph, suffix map, filter, coverage and source
assumptions, the top point has a bounded represented output that is unique
among all queried product triples in the whole result. -/
def top_forward_point : KDerivation (imp premises.encode
    (existsCode 5 (both (member 45 5)
      (both PASoundness.PAtoCompactMultiplicationTopCoverageTriple.topTriple.encode topUnique.encode)))) :=
  assemble premises.encode topUnique.encode (free_vacuity 5 premises (by decide))
    coverage_from_premises unique_from_witness

theorem top_forward_point_certificate : theoremCode (certificate top_forward_point) =
    imp premises.encode (existsCode 5 (both (member 45 5)
      (both PASoundness.PAtoCompactMultiplicationTopCoverageTriple.topTriple.encode topUnique.encode))) :=
  certificate_correct top_forward_point
end PASoundness.PAtoCompactMultiplicationTopForwardPoint
#print axioms PASoundness.PAtoCompactMultiplicationTopForwardPoint.top_forward_point
#print axioms PASoundness.PAtoCompactMultiplicationTopForwardPoint.top_forward_point_certificate
