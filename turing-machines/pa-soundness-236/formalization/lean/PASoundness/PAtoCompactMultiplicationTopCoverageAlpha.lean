import PASoundness.PAtoCompactMultiplicationTopCoverageWitness

/-! Capture-safe transport of the bounded top-row witnesses into the
product-style output and pair names. The same suffix-map and row edges are
retained. This proves no uniqueness, full product matrix, multiplication
totality, or PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopCoverageAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationTopCoverageWitness
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The same bounded row witness, with output name 5 and pair name 18. -/
def productStyleMatrix : Formula := namedBoth (.member 45 5)
  (namedBoth (graphFormula 6 3 5)
    (namedBoth (pairFormula 18 30 3) (graphFormula 64 18 5)))

/-- Capture-safe K alpha conversion, freeing the old pair label 5 before
reusing it as the output binder. No unique pair representative is assumed. -/
def witness_alpha : KDerivation
    (imp (Formula.ex 4 (.ex 5 boundedWitnessMatrix)).encode
      (Formula.ex 5 (.ex 18 productStyleMatrix)).encode) := by
  let A := boundedWitnessMatrix
  have hi := (existentialAlpha 5 18 A (by decide) (by decide) (by decide)).1
  have hl := existsCongr 4 hi
  have ho := (existentialAlpha 4 5 (.ex 18 (replace 5 18 A))
    (by decide) (by decide) (by decide)).1
  have hshape : replace 4 5 (.ex 18 (replace 5 18 A)) = .ex 18 productStyleMatrix := by decide
  rw [hshape] at ho
  simpa [A,Formula.encode] using (compose hl ho)

/-- A source member receives a bounded product-style witness with the same
map and represented row edges, under the displayed coverage and clean/filter
context. -/
def top_coverage_product_style : KDerivation
    (imp witnessContext.encode
      (imp (replace 0 31 (coverage 64)).encode (imp (member 31 3)
        (Formula.ex 5 (.ex 18 productStyleMatrix)).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 3,(replace 0 31 (coverage 64)).encode,witnessContext.encode]
  have hm : Context Γ (member 31 3) := .head _ _
  have hc : Context Γ (replace 0 31 (coverage 64)).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ witnessContext.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ (Formula.ex 4 (.ex 5 boundedWitnessMatrix)).encode :=
    .mp hm (.mp hc (.mp hh (.closed top_coverage)))
  exact .mp hr (.closed witness_alpha)

theorem witness_alpha_certificate : theoremCode (certificate witness_alpha) =
    imp (Formula.ex 4 (.ex 5 boundedWitnessMatrix)).encode
      (Formula.ex 5 (.ex 18 productStyleMatrix)).encode := certificate_correct witness_alpha

theorem top_coverage_product_style_certificate :
    theoremCode (certificate top_coverage_product_style) =
      imp witnessContext.encode
        (imp (replace 0 31 (coverage 64)).encode (imp (member 31 3)
          (Formula.ex 5 (.ex 18 productStyleMatrix)).encode)) :=
  certificate_correct top_coverage_product_style
end PASoundness.PAtoCompactMultiplicationTopCoverageAlpha
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageAlpha.witness_alpha
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageAlpha.top_coverage_product_style
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageAlpha.witness_alpha_certificate
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageAlpha.top_coverage_product_style_certificate
