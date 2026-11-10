import PASoundness.PAtoCompactSuccCongruenceEdgeSplit

/-! Capture-safe specialization of the supplied-adjunction edge split at
source label 4 and fresh target label 28. No graph existence or bijection is
asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccEdgeSplit4Target28
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceEdgeSplit

/-- The pointwise exact old-edge-or-new-edge split at (4,28). -/
def edge_split_4_28 : KDerivation (imp newGraph (imp newPair
    (imp (graphFormula 9 4 28).encode
      (either (graphFormula 6 4 28).encode (both (equal 4 0) (equal 28 1)))))) := by
  let f : Formula := .imp (graphFormula 9 2 3) conclusion
  let f4 : Formula := .imp (graphFormula 9 4 3)
    (namedEither (graphFormula 6 4 3) (namedBoth (.equal 4 0) (.equal 3 1)))
  let f428 : Formula := .imp (graphFormula 9 4 28)
    (namedEither (graphFormula 6 4 28) (namedBoth (.equal 4 0) (.equal 28 1)))
  have hi2 := universalInstance 2 4 (.all 3 f) (by decide) (by decide) (by decide)
  have he2 : CompactNamed.replace 2 4 (.all 3 f) = .all 3 f4 := by decide
  rw [he2] at hi2
  have hi3 := universalInstance 3 28 f4 (by decide) (by decide) (by decide)
  have he3 : CompactNamed.replace 3 28 f4 = f428 := by decide
  rw [he3] at hi3
  have hpoint : KDerivation (imp (allCode 2 (allCode 3 f.encode)) f428.encode) :=
    compose hi2 hi3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newPair,newGraph]
  have ha : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hp : Context Γ newPair := Context.head _ _
  have hall : Context Γ (allCode 2 (allCode 3 f.encode)) := by
    exact .mp hp (.mp ha (.closed edge_split_all))
  change Context Γ f428.encode
  exact .mp hall (.closed hpoint)

theorem edge_split_4_28_certificate : theoremCode (certificate edge_split_4_28) =
    imp newGraph (imp newPair (imp (graphFormula 9 4 28).encode
      (either (graphFormula 6 4 28).encode (both (equal 4 0) (equal 28 1))))) :=
  certificate_correct edge_split_4_28

end PASoundness.PAtoCompactSuccEdgeSplit4Target28

#print axioms PASoundness.PAtoCompactSuccEdgeSplit4Target28.edge_split_4_28
#print axioms PASoundness.PAtoCompactSuccEdgeSplit4Target28.edge_split_4_28_certificate
