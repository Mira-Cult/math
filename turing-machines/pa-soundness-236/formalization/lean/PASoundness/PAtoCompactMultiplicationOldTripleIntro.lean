import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactAdjunction
import PASoundness.CompactQuantifiers

/-! A finite K introduction for one old product triple, retaining the same
outer edge object. This is not graph collection, a row case split,
extensionality, multiplication totality, or a semantic soundness argument. -/
namespace PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactAdjunction
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The literal product triple at old graph name 10 and point labels 3,4,5. -/
def oldTriple : Formula := replace 6 10 (tripleFormula 3 4 5)

/-- The displayed outer member and pair formulas introduce the old triple
without assuming uniqueness of pair representatives. -/
def triple_from_shared_edge : KDerivation (imp (member 10 63)
    (imp (pairFormula 63 18 5).encode
      (imp (pairFormula 18 3 4).encode oldTriple.encode))) := by
  let graphBody : Formula := namedBoth (.member 10 19) (pairFormula 19 18 5)
  have hg := exists_variable_intro 19 63 graphBody (by decide) (by decide) (by decide)
  have hgShape : replace 19 63 graphBody = namedBoth (.member 10 63) (pairFormula 63 18 5) := by decide
  rw [hgShape] at hg
  have hg' : KDerivation (imp (both (member 10 63) (pairFormula 63 18 5).encode)
      (graphFormula 10 18 5).encode) := by
    change KDerivation (imp (both (member 10 63) (pairFormula 63 18 5).encode)
      (existsCode 19 graphBody.encode))
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hg
  let tripleBody : Formula := namedBoth (pairFormula 18 3 4) (graphFormula 10 18 5)
  have ht := existsIntroduce 18 tripleBody (by decide)
  have ht' : KDerivation (imp (both (pairFormula 18 3 4).encode (graphFormula 10 18 5).encode)
      oldTriple.encode) := by
    have hs : oldTriple = .ex 18 tripleBody := by decide
    rw [hs]
    simpa [tripleBody,namedBoth,Formula.not,Formula.encode,both,neg] using ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 18 3 4).encode,(pairFormula 63 18 5).encode,member 10 63]
  have hp : Context Γ (pairFormula 18 3 4).encode := .head _ _
  have he : Context Γ (pairFormula 63 18 5).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 10 63) := .hypothesis (by simp [Γ])
  have hgraph : Context Γ (graphFormula 10 18 5).encode :=
    .mp (Context.conjunctionIntro hm he) (.closed hg')
  exact .mp (Context.conjunctionIntro hp hgraph) (.closed ht')

theorem triple_from_shared_edge_certificate : theoremCode (certificate triple_from_shared_edge) =
    imp (member 10 63) (imp (pairFormula 63 18 5).encode
      (imp (pairFormula 18 3 4).encode oldTriple.encode)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldTripleIntro
#print axioms PASoundness.PAtoCompactMultiplicationOldTripleIntro.triple_from_shared_edge
#print axioms PASoundness.PAtoCompactMultiplicationOldTripleIntro.triple_from_shared_edge_certificate
