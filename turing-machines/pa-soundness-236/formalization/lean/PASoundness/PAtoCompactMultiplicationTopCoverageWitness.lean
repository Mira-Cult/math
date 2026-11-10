import PASoundness.PAtoCompactFixedFirstCoverageBase
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.PAtoCompactFilterInstantiation

/-! Pointwise top-row coverage. A supplied full-prefix row coverage, clean
suffix map, and literal filter yield an output in the whole result, retaining
the same map edge and pair/row witnesses. This proves existence only; uniqueness
and the full product matrix remain separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopCoverageWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The new result 45 is filtered outside old result 32 to suffix 40. -/
def suffixFilter : Formula := .all 35
  (namedFilterBody 45 40 35 (Formula.member 32 35).not)
/-- Fixed context shared by the witness-lifting steps. -/
def witnessContext : Formula := namedBoth suffixClean suffixFilter
/-- A row coverage witness before projecting its target bound. -/
def rowWitnessMatrix : Formula := namedBoth (graphFormula 6 3 4)
  (namedBoth (pairFormula 5 30 3) (graphFormula 64 5 4))
/-- The same witnesses, with membership in the new result added. -/
def boundedWitnessMatrix : Formula := namedBoth (.member 45 4) rowWitnessMatrix

private theorem filter_code : suffixFilter.encode =
    filterGraph 45 40 35 (neg (member 32 35)) := by rfl

/-- A clean map edge and the filter bound its output by the whole result. -/
def map_edge_in_result : KDerivation (imp witnessContext.encode
    (imp (graphFormula 6 3 4).encode (member 45 4))) := by
  let F := filterGraph 45 40 35 (neg (member 32 35))
  let P : Formula := (Formula.member 32 35).not
  have hi := filter_at 45 40 35 4 P (by decide) (by decide) (by decide) (by decide) (by decide)
  have hfilter : KDerivation (imp F
      (both (imp (member 40 4) (both (member 45 4) (neg (member 32 4))))
        (imp (both (member 45 4) (neg (member 32 4))) (member 40 4)))) := by
    simpa [F,P,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 3 4).encode,witnessContext.encode]
  have he : Context Γ (graphFormula 6 3 4).encode := .head _ _
  have hh : Context Γ witnessContext.encode := .hypothesis (by simp [Γ])
  have hh' : Context Γ (both suffixClean.encode F) := by
    simpa [witnessContext,namedBoth,Formula.not,Formula.encode,both,neg,filter_code,F] using hh
  have hm40 : Context Γ (member 40 4) := Context.conjunctionRight
    (.mp he (.mp (Context.conjunctionLeft hh') (.closed (clean_endpoints 3 4 (by decide)))))
  exact Context.conjunctionLeft
    (.mp hm40 (Context.conjunctionLeft (.mp (Context.conjunctionRight hh') (.closed hfilter))))

/-- The same row witness obtains the whole-result output bound. -/
def bound_point : KDerivation
    (imp witnessContext.encode (imp rowWitnessMatrix.encode boundedWitnessMatrix.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [rowWitnessMatrix.encode,witnessContext.encode]
  have hw : Context Γ rowWitnessMatrix.encode := .head _ _
  have hh : Context Γ witnessContext.encode := .hypothesis (by simp [Γ])
  have hw' : Context Γ (both (graphFormula 6 3 4).encode
      (both (pairFormula 5 30 3).encode (graphFormula 64 5 4).encode)) := by
    simpa [rowWitnessMatrix,namedBoth,Formula.not,Formula.encode,both,neg] using hw
  have hm : Context Γ (member 45 4) :=
    .mp (Context.conjunctionLeft hw') (.mp hh (.closed map_edge_in_result))
  have hb := Context.conjunctionIntro hm hw
  simpa [boundedWitnessMatrix,namedBoth,Formula.not,Formula.encode,both,neg] using hb

/-- Retain both existential witnesses while adding the output bound. -/
def bound_row_witness : KDerivation (imp witnessContext.encode
    (imp (Formula.ex 4 (.ex 5 rowWitnessMatrix)).encode
      (Formula.ex 4 (.ex 5 boundedWitnessMatrix)).encode)) := by
  have h5 := conditionalExistsCongr 5 (witnessContext.vacuity 5 (by decide)) bound_point
  have h4 := conditionalExistsCongr 4 (witnessContext.vacuity 4 (by decide)) h5
  simpa [Formula.encode] using h4

/-- Full-prefix row coverage at a source member constructs an output in the
whole result, retaining a represented row edge and its map edge. -/
def top_coverage : KDerivation
    (imp witnessContext.encode
      (imp (replace 0 31 (coverage 64)).encode (imp (member 31 3)
        (Formula.ex 4 (.ex 5 boundedWitnessMatrix)).encode))) := by
  let B : Formula := .imp (namedBoth (.member 31 3) (.member 31 3))
    (.ex 4 (.ex 5 rowWitnessMatrix))
  have hshape : replace 0 31 (coverage 64) = .all 3 B := by decide
  have hs := allSpecialize 3 B (by decide)
  change KDerivation (imp (Formula.all 3 B).encode B.encode) at hs
  rw [← hshape] at hs
  have hs' : KDerivation (imp (replace 0 31 (coverage 64)).encode
      (imp (both (member 31 3) (member 31 3))
        (Formula.ex 4 (.ex 5 rowWitnessMatrix)).encode)) := by
    simpa [B,namedBoth,Formula.not,Formula.encode,both,neg] using hs
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 3,(replace 0 31 (coverage 64)).encode,witnessContext.encode]
  have hm : Context Γ (member 31 3) := .head _ _
  have hc : Context Γ (replace 0 31 (coverage 64)).encode := .hypothesis (by simp [Γ])
  have hh : Context Γ witnessContext.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ (Formula.ex 4 (.ex 5 rowWitnessMatrix)).encode :=
    .mp (Context.conjunctionIntro hm hm) (.mp hc (.closed hs'))
  exact .mp hr (.mp hh (.closed bound_row_witness))

theorem top_coverage_certificate : theoremCode (certificate top_coverage) =
    imp witnessContext.encode
      (imp (replace 0 31 (coverage 64)).encode (imp (member 31 3)
        (Formula.ex 4 (.ex 5 boundedWitnessMatrix)).encode)) :=
  certificate_correct top_coverage
end PASoundness.PAtoCompactMultiplicationTopCoverageWitness
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageWitness.map_edge_in_result
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageWitness.bound_point
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageWitness.bound_row_witness
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageWitness.top_coverage
#print axioms PASoundness.PAtoCompactMultiplicationTopCoverageWitness.top_coverage_certificate
