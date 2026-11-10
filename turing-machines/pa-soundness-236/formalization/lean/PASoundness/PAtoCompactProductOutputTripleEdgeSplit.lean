import PASoundness.PAtoCompactProductMatchAdjoinSplit
import PASoundness.PAtoCompactProductOutputTripleExtension

/-! A new edge in the single-triple adjunction is old or has the selected
nested-pair coordinate and selected image output. The coordinate-pair
comparison and triple-invariant coverage remain separate obligations. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputTripleEdgeSplit

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchAdjoinSplit

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def alphaBody : Formula := namedBoth
  (.imp (.member 9 16) (namedEither (.equal 16 12) (.member 58 16)))
  (.imp (namedEither (.equal 16 12) (.member 58 16)) (.member 9 16))
def alphaTarget : Formula := namedBoth
  (.imp (.member 9 18) (namedEither (.equal 18 12) (.member 58 18)))
  (.imp (namedEither (.equal 18 12) (.member 58 18)) (.member 9 18))

def adjoin_alpha : KDerivation (imp (adjoinCode 58 12 9 16) (adjoinCode 58 12 9 18)) := by
  have h := (universalAlpha 16 18 alphaBody (by decide) (by decide) (by decide)).1
  have he : replace 16 18 alphaBody = alphaTarget := by decide
  rw [he] at h
  simpa [alphaBody, alphaTarget, adjoinCode, namedBoth, namedEither,
    CompactNamed.Formula.encode, both, neg, either] using h

def splitConclusion : Formula := namedEither (graphFormula 58 55 60)
  (namedBoth (.equal 55 11) (.equal 60 33))
def splitFrame : Formula := .imp (namedAdjoin 58 12 9 18)
  (.imp (pairFormula 12 11 33) (.imp (graphFormula 9 55 60) splitConclusion))

theorem split_frame_shape : replace 3 60 (replace 2 55 (replace 10 11
    (replace 17 9 (replace 16 12 (replace 9 58 (replace 12 33
      PAtoCompactProductMatchAdjoinSplit.sourceFrame)))))) = splitFrame := by decide

/-- A new edge either was already present or uses the selected pair
representative and image output. Test-name conversion is an explicit K proof. -/
def triple_edge_split : KDerivation (imp (adjoinCode 58 12 9 16)
    (imp (pairFormula 12 11 33).encode (imp (graphFormula 9 55 60).encode
      (either (graphFormula 58 55 60).encode (both (equal 55 11) (equal 60 33)))))) := by
  let F := PAtoCompactProductMatchAdjoinSplit.sourceFrame
  have h0 : KDerivation F.encode := by
    simpa [F, PAtoCompactProductMatchAdjoinSplit.sourceFrame,
      PAtoCompactCompositionNoSpurious.adjacent, PAtoCompactCompositionNoSpurious.selected,
      PAtoCompactCompositionNoSpurious.conclusion, namedAdjoin, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, adjoinCode, both, neg, either] using
        PAtoCompactCompositionNoSpurious.no_spurious_edge
  have h1 := replace_derivation 12 33 F (by decide) (by decide) h0
  have h2 := replace_derivation 9 58 (replace 12 33 F) (by decide) (by decide) h1
  have h3 := replace_derivation 16 12 (replace 9 58 (replace 12 33 F)) (by decide) (by decide) h2
  have h4 := replace_derivation 17 9 (replace 16 12 (replace 9 58 (replace 12 33 F))) (by decide) (by decide) h3
  have h5 := replace_derivation 10 11 (replace 17 9 (replace 16 12 (replace 9 58 (replace 12 33 F)))) (by decide) (by decide) h4
  have h6 := replace_derivation 2 55 (replace 10 11 (replace 17 9 (replace 16 12 (replace 9 58 (replace 12 33 F))))) (by decide) (by decide) h5
  have h7 := replace_derivation 3 60 (replace 2 55 (replace 10 11 (replace 17 9 (replace 16 12 (replace 9 58 (replace 12 33 F)))))) (by decide) (by decide) h6
  have hs : KDerivation (imp (adjoinCode 58 12 9 18)
      (imp (pairFormula 12 11 33).encode (imp (graphFormula 9 55 60).encode
        (either (graphFormula 58 55 60).encode (both (equal 55 11) (equal 60 33)))))) := by
    simpa [F, split_frame_shape, splitFrame, splitConclusion, namedAdjoin, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, adjoinCode, both, neg, either] using h7
  exact compose adjoin_alpha hs

theorem triple_edge_split_certificate : theoremCode (certificate triple_edge_split) =
    imp (adjoinCode 58 12 9 16) (imp (pairFormula 12 11 33).encode
      (imp (graphFormula 9 55 60).encode
        (either (graphFormula 58 55 60).encode (both (equal 55 11) (equal 60 33))))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputTripleEdgeSplit

#print axioms PASoundness.PAtoCompactProductOutputTripleEdgeSplit.adjoin_alpha
#print axioms PASoundness.PAtoCompactProductOutputTripleEdgeSplit.triple_edge_split
#print axioms PASoundness.PAtoCompactProductOutputTripleEdgeSplit.triple_edge_split_certificate
