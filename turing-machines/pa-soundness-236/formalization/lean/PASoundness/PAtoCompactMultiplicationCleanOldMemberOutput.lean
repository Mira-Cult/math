import PASoundness.PAtoCompactProductCleanEndpointsPoint

/-! Capture-safe specialization of the product-cleanliness endpoint theorem
to old graph 10 and domains 30,31,32. This is a K pointwise proof and does not
construct graph witnesses, prove row coverage, or establish multiplication.
Adapted from the untracked ProductOldSuffixExclusion draft; the latter is not
an import or proof premise. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactProductCleanEndpointsPoint
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Old graph 10 contains only product edges with endpoints in 30,31,32. -/
def oldClean : Formula := .all 19 (.imp (.member 10 19)
  (replace 2 32 (replace 1 31 (replace 0 30 (cleanPredicate 19)))))
/-- The actual queried nested edge at 63 has output 5. -/
def query63 : Formula := replace 19 63 queryPairs
private def clean63 : Formula := replace 19 63
  (replace 2 32 (replace 1 31 (replace 0 30 (cleanPredicate 19))))
private def pointFormula : Formula := .imp queryPairs (.imp (cleanPredicate 19) endpoints)
private def point30 : Formula := replace 0 30 pointFormula
private def point31 : Formula := replace 1 31 point30
private def point32 : Formula := replace 2 32 point31
private def point63 : Formula := replace 19 63 point32

private def relabel_point : KDerivation point63.encode := by
  have h0 : KDerivation pointFormula.encode := endpoint_of_clean_member
  have h1 : KDerivation point30.encode :=
    .mp (.generalize 0 h0) (universalInstance 0 30 pointFormula (by decide) (by decide) (by decide))
  have h2 : KDerivation point31.encode :=
    .mp (.generalize 1 h1) (universalInstance 1 31 point30 (by decide) (by decide) (by decide))
  have h3 : KDerivation point32.encode :=
    .mp (.generalize 2 h2) (universalInstance 2 32 point31 (by decide) (by decide) (by decide))
  exact .mp (.generalize 19 h3) (universalInstance 19 63 point32 (by decide) (by decide) (by decide))

/-- From the same clean old graph member and queried pair descriptions, the
queried output is a member of the old result. -/
def old_output : KDerivation (imp oldClean.encode
    (imp (member 10 63) (imp query63.encode (member 32 5)))) := by
  let F : Formula := .imp (.member 10 19)
    (replace 2 32 (replace 1 31 (replace 0 30 (cleanPredicate 19))))
  have hi := universalInstance 19 63 F (by decide) (by decide) (by decide)
  have hs : replace 19 63 F = .imp (.member 10 63) clean63 := by decide
  rw [hs] at hi
  have hp : KDerivation (imp query63.encode (imp clean63.encode
      (both (member 30 3) (both (member 31 4) (member 32 5))))) := by
    have hshape : point63 = .imp query63 (.imp clean63
      (namedBoth (.member 30 3) (namedBoth (.member 31 4) (.member 32 5)))) := by decide
    have h := relabel_point
    rw [hshape] at h
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [query63.encode,member 10 63,oldClean.encode]
  have hq : Context Γ query63.encode := .head _ _
  have hm : Context Γ (member 10 63) := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hclean : Context Γ clean63.encode := .mp hm (.mp hc (.closed hi))
  have hp' : Context Γ (both (member 30 3) (both (member 31 4) (member 32 5))) :=
    Context.mp hclean (Context.mp hq (.closed hp))
  exact Context.conjunctionRight (Context.conjunctionRight hp')

/-- All three endpoint bounds of the queried same clean edge. -/
def old_endpoints : KDerivation (imp oldClean.encode
    (imp (member 10 63) (imp query63.encode
      (both (member 30 3) (both (member 31 4) (member 32 5)))))) := by
  let F : Formula := .imp (.member 10 19)
    (replace 2 32 (replace 1 31 (replace 0 30 (cleanPredicate 19))))
  have hi := universalInstance 19 63 F (by decide) (by decide) (by decide)
  have hs : replace 19 63 F = .imp (.member 10 63) clean63 := by decide
  rw [hs] at hi
  have hp : KDerivation (imp query63.encode (imp clean63.encode
      (both (member 30 3) (both (member 31 4) (member 32 5))))) := by
    have hshape : point63 = .imp query63 (.imp clean63
      (namedBoth (.member 30 3) (namedBoth (.member 31 4) (.member 32 5)))) := by decide
    have h := relabel_point
    rw [hshape] at h
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [query63.encode,member 10 63,oldClean.encode]
  have hq : Context Γ query63.encode := .head _ _
  have hm : Context Γ (member 10 63) := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hclean : Context Γ clean63.encode := .mp hm (.mp hc (.closed hi))
  have hp' : Context Γ (both (member 30 3) (both (member 31 4) (member 32 5))) :=
    Context.mp hclean (Context.mp hq (.closed hp))
  exact hp'

end PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput.old_output
#print axioms PASoundness.PAtoCompactMultiplicationCleanOldMemberOutput.old_endpoints
