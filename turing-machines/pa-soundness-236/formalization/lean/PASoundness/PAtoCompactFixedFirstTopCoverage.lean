import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactGraphWitnessRules

/-! A single top-index coverage witness for the fixed-first-coordinate row
invariant. Given the displayed F-edge, inner pair, outer pair and membership,
K introduces the exact nested existential required by coverage. This does
not prove the full row invariant, row collection or multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstTopCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The coverage body for source index 0, F graph 6, new row graph 7,
and fixed first coordinate 30. -/
def topCoverage : Formula := .ex 4 (.ex 5
  (namedBoth (graphFormula 6 0 4)
    (namedBoth (pairFormula 5 30 0) (graphFormula 7 5 4))))

private def added_graph_edge : KDerivation
    (imp (member 7 13) (imp (pairFormula 13 12 4).encode (graphFormula 7 12 4).encode)) := by
  let f : Formula := namedBoth (.member 7 19) (pairFormula 19 12 4)
  have hi := exists_variable_intro 19 13 f (by decide) (by decide) (by decide)
  have hr : replace 19 13 f = namedBoth (.member 7 13) (pairFormula 13 12 4) := by decide
  rw [hr] at hi
  change KDerivation (imp (both (member 7 13) (pairFormula 13 12 4).encode)
    (graphFormula 7 12 4).encode) at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 13 12 4).encode,member 7 13]
  have hp : Context Γ (pairFormula 13 12 4).encode := .head _ _
  have hm : Context Γ (member 7 13) := .hypothesis (by simp [Γ])
  exact .mp (Context.conjunctionIntro hm hp) (.closed hi)

/-- The supplied point-edge and two pair objects produce the coverage
existential. No uniqueness of pair representatives is assumed. -/
def top_coverage_from_witnesses : KDerivation
    (imp (graphFormula 6 0 4).encode
      (imp (pairFormula 12 30 0).encode
        (imp (pairFormula 13 12 4).encode
          (imp (member 7 13) topCoverage.encode)))) := by
  let body : Formula := namedBoth (graphFormula 6 0 4)
    (namedBoth (pairFormula 5 30 0) (graphFormula 7 5 4))
  have hi5 := exists_variable_intro 5 12 body (by decide) (by decide) (by decide)
  have hr : replace 5 12 body = namedBoth (graphFormula 6 0 4)
      (namedBoth (pairFormula 12 30 0) (graphFormula 7 12 4)) := by decide
  rw [hr] at hi5
  have hi5' : KDerivation (imp
      (both (graphFormula 6 0 4).encode
        (both (pairFormula 12 30 0).encode (graphFormula 7 12 4).encode))
      (existsCode 5 body.encode)) := by
    simpa [body,namedBoth,Formula.encode,both,neg] using hi5
  have hi4 : KDerivation (imp (existsCode 5 body.encode) topCoverage.encode) := by
    have h := existsIntroduce 4 (.ex 5 body) (by decide)
    simpa [topCoverage,body,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 7 13,(pairFormula 13 12 4).encode,
    (pairFormula 12 30 0).encode,(graphFormula 6 0 4).encode]
  have hm : Context Γ (member 7 13) := .head _ _
  have hp : Context Γ (pairFormula 13 12 4).encode := .hypothesis (by simp [Γ])
  have hq : Context Γ (pairFormula 12 30 0).encode := .hypothesis (by simp [Γ])
  have hf : Context Γ (graphFormula 6 0 4).encode := .hypothesis (by simp [Γ])
  have he : Context Γ (graphFormula 7 12 4).encode := .mp hp (.mp hm (.closed added_graph_edge))
  have hb := Context.conjunctionIntro hf (Context.conjunctionIntro hq he)
  exact .mp (.mp hb (.closed hi5')) (.closed hi4)

theorem top_coverage_from_witnesses_certificate :
    theoremCode (certificate top_coverage_from_witnesses) =
      imp (graphFormula 6 0 4).encode
        (imp (pairFormula 12 30 0).encode
          (imp (pairFormula 13 12 4).encode
            (imp (member 7 13) topCoverage.encode))) :=
  certificate_correct top_coverage_from_witnesses
end PASoundness.PAtoCompactFixedFirstTopCoverage
#print axioms PASoundness.PAtoCompactFixedFirstTopCoverage.top_coverage_from_witnesses
#print axioms PASoundness.PAtoCompactFixedFirstTopCoverage.top_coverage_from_witnesses_certificate
