import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.CompactNamed
import PASoundness.PAtoCompactZeroSuccessor

/-! Capture-safe extraction of the actual inner pair and outer edge objects
from one queried product triple. This constructs literal K derivations; it
neither splits a graph into old/new branches nor establishes row collection,
multiplication totality, extensionality or semantic soundness. -/
namespace PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The exact queried product triple with represented graph renamed 6→64. -/
def queriedTriple : Formula := replace 6 64 (tripleFormula 3 4 5)
/-- The queried coordinate pair, retaining inner pair name 18. -/
def coordinates : Formula := pairFormula 18 3 4
/-- One member of graph 64 is the corresponding outer pair. -/
def outerBody (e : Nat) : Formula := namedBoth (.member 64 e) (pairFormula e 18 5)
/-- Both actual witnesses are retained, with fresh outer-edge name 63. -/
def expandedTriple : Formula := .ex 18 (.ex 63 (namedBoth coordinates (outerBody 63)))

theorem queried_shape : queriedTriple = .ex 18 (namedBoth coordinates (.ex 19 (outerBody 19))) := by decide

/-- The underlying graph-existential is capture-safely rebound to 63. -/
def graph_alpha : KDerivation
    (imp (existsCode 19 (outerBody 19).encode) (existsCode 63 (outerBody 63).encode)) := by
  have h := (existentialAlpha 19 63 (outerBody 19) (by decide) (by decide) (by decide)).1
  have hs : replace 19 63 (outerBody 19) = outerBody 63 := by decide
  rw [hs] at h
  exact h

private def pairing : KDerivation
    (imp coordinates.encode (imp (outerBody 63).encode
      (namedBoth coordinates (outerBody 63)).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(outerBody 63).encode,coordinates.encode]
  have hb : Context Γ (outerBody 63).encode := .head _ _
  have hc : Context Γ coordinates.encode := .hypothesis (by simp [Γ])
  simpa [namedBoth,Formula.not,Formula.encode,both,neg] using (Context.conjunctionIntro hc hb)

private def inside : KDerivation
    (imp (namedBoth coordinates (.ex 19 (outerBody 19))).encode
      (existsCode 63 (namedBoth coordinates (outerBody 63)).encode)) := by
  have hv := coordinates.vacuity 63 (by decide)
  have hc := conditionalExistsCongr 63 hv pairing
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(namedBoth coordinates (.ex 19 (outerBody 19))).encode]
  have h : Context Γ (both coordinates.encode (existsCode 19 (outerBody 19).encode)) := by
    simpa [Γ,namedBoth,Formula.not,Formula.encode,both,neg] using
      (Context.head [] (namedBoth coordinates (.ex 19 (outerBody 19))).encode)
  have hP := Context.conjunctionLeft h
  have hg := Context.conjunctionRight h
  have h63 := Context.mp hg (.closed graph_alpha)
  exact .mp h63 (.mp hP (.closed hc))

/-- Every queried product triple contains an actual graph member 63 and its
inner pair 18 satisfying the displayed pair formulas, all under a single
existential for that same outer object. -/
def triple_to_expanded : KDerivation (imp queriedTriple.encode expandedTriple.encode) := by
  have h := existsCongr 18 inside
  rw [queried_shape]
  simpa [expandedTriple,Formula.encode] using h

theorem triple_to_expanded_certificate : theoremCode (certificate triple_to_expanded) =
    imp queriedTriple.encode expandedTriple.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
#print axioms PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha.queried_shape
#print axioms PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha.graph_alpha
#print axioms PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha.triple_to_expanded
#print axioms PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha.triple_to_expanded_certificate
