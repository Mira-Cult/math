import PASoundness.PAtoCompactSuccCongruenceEdgeSplit

/-! Alpha-align the checked uniform edge split to binders 28 and 29. This
retains the supplied adjunction and pair hypotheses and does not establish
clean graph, collection or successor congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceEdgeAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceEdgeSplit

/-- Uniform edge split at names fresh for the successor bijection's binders. -/
def namedSplit : Formula := .all 28 (.all 29
  (.imp (graphFormula 9 28 29)
    (namedEither (graphFormula 6 28 29) (namedBoth (.equal 28 0) (.equal 29 1)))))

/-- The exact 2/3-quantified theorem implies its capture-safe 28/29 form. -/
def edge_split_alpha : KDerivation (imp newGraph (imp newPair namedSplit.encode)) := by
  let body : Formula := .imp (graphFormula 9 2 3) conclusion
  let body29 : Formula := .imp (graphFormula 9 2 29)
    (namedEither (graphFormula 6 2 29) (namedBoth (.equal 2 0) (.equal 29 1)))
  let tail : Formula := .all 29 (.imp (graphFormula 9 28 29)
    (namedEither (graphFormula 6 28 29) (namedBoth (.equal 28 0) (.equal 29 1))))
  have h3 := (universalAlpha 3 29 body (by decide) (by decide) (by decide)).1
  have h3syntax : replace 3 29 body = body29 := by decide
  rw [h3syntax] at h3
  have h3lift := allCongr 2 h3
  have h2 := (universalAlpha 2 28 (.all 29 body29) (by decide) (by decide) (by decide)).1
  have h2syntax : replace 2 28 (.all 29 body29) = tail := by decide
  rw [h2syntax] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newPair,newGraph]
  have hp : Context Γ newPair := Context.head _ _
  have hg : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode 2 (allCode 3 body.encode)) :=
    .mp hp (.mp hg (.closed edge_split_all))
  have hresult : Context Γ (allCode 28 tail.encode) := .mp (.mp hall (.closed h3lift)) (.closed h2)
  exact hresult

theorem edge_split_alpha_certificate : theoremCode (certificate edge_split_alpha) =
    imp newGraph (imp newPair namedSplit.encode) := certificate_correct edge_split_alpha

end PASoundness.PAtoCompactSuccCongruenceEdgeAlpha

#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeAlpha.edge_split_alpha
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeAlpha.edge_split_alpha_certificate
