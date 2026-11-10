import PASoundness.PAtoCompactMultiplicationTopCoverageAlpha
import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactFreeVacuity

/-! Repackage the actual bounded top-row witness as a product-style triple,
retaining the very same suffix-map edge and bounded output. This constructs
no uniqueness proof, complete product matrix, or multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopCoverageTriple
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationTopCoverageWitness
open PASoundness.PAtoCompactMultiplicationTopCoverageAlpha
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Product triple through new graph 64, using fixed top 30, row point 3,
and output 5. This is the literal product triple with its graph name moved. -/
def topTriple : Formula := replace 6 64 (tripleFormula 30 3 5)

/-- The same output is bounded by 45, connected by the supplied map 6, and
represented by a product triple in graph 64. -/
def tripleWitness : Formula := namedBoth (.member 45 5)
  (namedBoth (graphFormula 6 3 5) topTriple)

private def inner : Formula := namedBoth (pairFormula 18 30 3) (graphFormula 64 18 5)
private theorem triple_shape : topTriple = .ex 18 inner := by decide

private def point : KDerivation (imp productStyleMatrix.encode tripleWitness.encode) := by
  have hintro := existsIntroduce 18 inner (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [productStyleMatrix.encode]
  have h : Context Γ productStyleMatrix.encode := .head _ _
  have hh : Context Γ (both (member 45 5) (both (graphFormula 6 3 5).encode inner.encode)) := by
    simpa [productStyleMatrix,inner,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have he : Context Γ (existsCode 18 inner.encode) :=
    .mp (Context.conjunctionRight (Context.conjunctionRight hh)) (.closed hintro)
  have hout := Context.conjunctionIntro (Context.conjunctionLeft hh)
    (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hh)) he)
  simpa [tripleWitness,triple_shape,namedBoth,Formula.not,Formula.encode,both,neg] using hout

/-- Eliminate the pair witness only after introducing it as the witness for
the product triple; the output and suffix-map edge remain the same. -/
def repackage_pair : KDerivation (imp (existsCode 18 productStyleMatrix.encode)
    tripleWitness.encode) := by
  have hv := free_vacuity 18 tripleWitness (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim hv (.closed (.generalize 18 point)) (.head [] _)

/-- The repackage is lifted over the same existential output witness. -/
def repackage_output : KDerivation
    (imp (Formula.ex 5 (.ex 18 productStyleMatrix)).encode
      (Formula.ex 5 tripleWitness).encode) := by
  simpa [Formula.encode] using existsCongr 5 repackage_pair

/-- Under clean suffix-map/filter and full-prefix row-coverage assumptions,
every source member has a bounded product-style top-row triple. -/
def top_coverage_triple : KDerivation
    (imp witnessContext.encode
      (imp (replace 0 31 (coverage 64)).encode (imp (member 31 3)
        (Formula.ex 5 tripleWitness).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 3,(replace 0 31 (coverage 64)).encode,witnessContext.encode]
  have hm : Context Γ (member 31 3) := .head _ _
  have hc : Context Γ (replace 0 31 (coverage 64)).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ witnessContext.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (Formula.ex 5 (.ex 18 productStyleMatrix)).encode :=
    .mp hm (.mp hc (.mp hh (.closed top_coverage_product_style)))
  exact .mp hw (.closed repackage_output)

theorem top_coverage_triple_certificate : theoremCode (certificate top_coverage_triple) =
    imp witnessContext.encode
      (imp (replace 0 31 (coverage 64)).encode (imp (member 31 3)
        (Formula.ex 5 tripleWitness).encode)) := certificate_correct top_coverage_triple
end PASoundness.PAtoCompactMultiplicationTopCoverageTriple
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageTriple.repackage_pair
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageTriple.repackage_output
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageTriple.top_coverage_triple
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageTriple.top_coverage_triple_certificate
