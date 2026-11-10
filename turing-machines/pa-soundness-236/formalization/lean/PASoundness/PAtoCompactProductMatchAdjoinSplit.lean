import PASoundness.PAtoCompactCompositionNoSpurious
import PASoundness.PAtoCompactProductMatchEndpointEdge

/-! Inspect an adjoined product-match graph edge. It is either an old edge
or has the selected source and target coordinates. This does not yet prove
the complete backward coverage invariant. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchAdjoinSplit

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactCompositionNoSpurious
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactProductMatchPartialBase
open PASoundness.PAtoCompactProductMatchInsideImage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceFrame : Formula := .imp (namedAdjoin 9 16 17 18)
  (.imp (pairFormula 16 10 12) (.imp (graphFormula 17 2 3) conclusion))

def targetConclusion : Formula := namedEither (graphFormula 58 56 57)
  (namedBoth (.equal 56 74) (.equal 57 35))

def targetFrame : Formula := .imp (namedAdjoin 58 16 17 18)
  (.imp (pairFormula 16 74 35) (.imp (graphFormula 17 56 57) targetConclusion))

theorem relocation_shape :
    replace 3 57 (replace 2 56 (replace 12 35 (replace 10 74 (replace 9 58 sourceFrame)))) =
      targetFrame := by decide

/-- An adjoined edge is old or has exactly the selected coordinates. -/
def edge_split : KDerivation (imp (adjoinCode 58 16 17 18)
    (imp (pairFormula 16 74 35).encode (imp (graphFormula 17 56 57).encode
      (either (graphFormula 58 56 57).encode (both (equal 56 74) (equal 57 35)))))) := by
  have h0 : KDerivation sourceFrame.encode := by
    simpa [sourceFrame, adjacent, selected, conclusion, namedAdjoin, namedBoth, namedEither,
      Formula.not, Formula.encode, adjoinCode, both, neg, either] using no_spurious_edge
  have h1 := replace_derivation 9 58 sourceFrame (by decide) (by decide) h0
  have h2 := replace_derivation 10 74 (replace 9 58 sourceFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 12 35 (replace 10 74 (replace 9 58 sourceFrame))
    (by decide) (by decide) h2
  have h4 := replace_derivation 2 56 (replace 12 35 (replace 10 74 (replace 9 58 sourceFrame)))
    (by decide) (by decide) h3
  have h5 := replace_derivation 3 57
    (replace 2 56 (replace 12 35 (replace 10 74 (replace 9 58 sourceFrame))))
    (by decide) (by decide) h4
  rw [relocation_shape] at h5
  simpa [targetFrame, targetConclusion, namedAdjoin, namedBoth, namedEither,
    Formula.not, Formula.encode, adjoinCode, both, neg, either] using h5

/-- Retarget the selected path along both coordinate equalities. -/
def selected_path_at_query : KDerivation (imp (equal 56 74) (imp (equal 57 35)
    (imp selectedPath.encode matchAt.encode))) := by
  have h1 := (equalityReplace 74 56 selectedPath (by decide) (by decide)).1
  have h2 := (equalityReplace 35 57 (replace 74 56 selectedPath) (by decide) (by decide)).1
  have hs : replace 35 57 (replace 74 56 selectedPath) = matchAt := by decide
  rw [hs] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [selectedPath.encode,equal 57 35,equal 56 74]
  have hp : Context Γ selectedPath.encode := .head _ _
  have hy : Context Γ (equal 57 35) := .hypothesis (by simp [Γ])
  have hx : Context Γ (equal 56 74) := .hypothesis (by simp [Γ])
  have hx' : Context Γ (equal 74 56) := Context.eqSymm hx
  have hy' : Context Γ (equal 35 57) := Context.eqSymm hy
  have h := Context.mp hp (Context.mp hx' (.closed h1))
  exact .mp h (.mp hy' (.closed h2))

theorem edge_split_certificate : theoremCode (certificate edge_split) =
    imp (adjoinCode 58 16 17 18) (imp (pairFormula 16 74 35).encode
      (imp (graphFormula 17 56 57).encode
        (either (graphFormula 58 56 57).encode (both (equal 56 74) (equal 57 35))))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchAdjoinSplit

#print axioms PASoundness.PAtoCompactProductMatchAdjoinSplit.edge_split
#print axioms PASoundness.PAtoCompactProductMatchAdjoinSplit.selected_path_at_query
#print axioms PASoundness.PAtoCompactProductMatchAdjoinSplit.edge_split_certificate
