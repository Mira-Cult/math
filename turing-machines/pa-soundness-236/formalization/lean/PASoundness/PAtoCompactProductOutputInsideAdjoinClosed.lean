import PASoundness.PAtoCompactProductOutputGraphIntro
import PASoundness.PAtoCompactProductOutputInsideExtension
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactFreeVacuity

/-! Consume the actual selected point and single-triple adjunction witnesses,
then apply the proved guarded invariant and capture-safe graph introduction.
This is a local inside-extension result; the candidate induction assembly is
separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputInsideAdjoinClosed

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsideStep
open PASoundness.PAtoCompactProductOutputInsideSelected PASoundness.PAtoCompactProductOutputTripleExtension
open PASoundness.PAtoCompactProductOutputTripleNoGarbage PASoundness.PAtoCompactProductOutputSameSourceTriple
open PASoundness.PAtoCompactProductOutputAdjoinInvariant9 PASoundness.PAtoCompactProductOutputGraphIntro

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def retained : Formula := namedBoth (namedSuccessor 74 59 76) oldInvariant
def innerPair : Formula := pairFormula 11 30 31
def outerPair : Formula := pairFormula 12 11 33
def extensionBody : Formula := namedBoth (namedAdjoin 58 12 9 16)
  (namedBoth selectedTriple newRetained)
def guard9 : Formula := namedBoth retained (namedBoth relocatedBody (namedBoth innerPair outerPair))
def guard12 : Formula := namedBoth retained (namedBoth relocatedBody innerPair)
def guard11 : Formula := namedBoth retained relocatedBody
def result : Formula := .ex 58 partialInvariant

theorem new_statement_expanded : newStatement = .ex 11 (namedBoth innerPair (.ex 12
    (namedBoth outerPair (.ex 9 extensionBody)))) := by decide

/-- For the exact old graph, selected point, two pairs and new graph, the
quantified invariant holds and the new graph may be existentially packaged. -/
noncomputable def at_graph : KDerivation (imp guard9.encode (imp extensionBody.encode result.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [extensionBody.encode,guard9.encode]
  have he : Context Γ extensionBody.encode := .head _ _
  have hg : Context Γ guard9.encode := .hypothesis (by simp [Γ])
  have he' : Context Γ (both (adjoinCode 58 12 9 16) (both selectedTriple.encode newRetained.encode)) := by
    simpa [extensionBody, namedAdjoin, namedBoth, namedEither, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, adjoinCode, both, neg, either] using he
  have hg' : Context Γ (both retained.encode (both relocatedBody.encode (both innerPair.encode outerPair.encode))) := by
    simpa [guard9, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hr : Context Γ (both (successorCode 74 59 76) oldInvariant.encode) := by
    simpa [retained, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using Context.conjunctionLeft hg'
  have hn : Context Γ PAtoCompactProductOutputTripleNoGarbage.guard.encode := by
    simpa [PAtoCompactProductOutputTripleNoGarbage.guard, innerPair, outerPair, namedAdjoin,
      namedBoth, namedEither, CompactNamed.Formula.not, CompactNamed.Formula.encode, adjoinCode, both, neg, either] using
      Context.conjunctionIntro (Context.conjunctionLeft he')
        (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg')))
          (Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))))
  have hj : Context Γ jointGuard.encode := by
    simpa [jointGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using
      Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hg'))
        (Context.conjunctionIntro (Context.conjunctionLeft hr)
          (Context.conjunctionIntro hn (Context.conjunctionIntro (Context.conjunctionRight hr)
            (Context.conjunctionRight he'))))
  have hi := Context.mp hj (.closed adjoin_invariant9)
  simpa [result, CompactNamed.Formula.encode] using Context.mp hi (.closed introduce_graph)

/-- Eliminate the new graph and both pair representatives while keeping the
selected point and the old graph fixed. -/
noncomputable def selected_adjoin_closed : KDerivation (imp retained.encode
    (imp relocatedBody.encode (imp newStatement.encode result.encode))) := by
  have h9 := guarded_exists_left 9 guard9.encode extensionBody.encode result.encode
    (free_vacuity 9 guard9 (by decide)) (free_vacuity 9 result (by decide)) at_graph
  have h12point : KDerivation (imp guard12.encode (imp (namedBoth outerPair (.ex 9 extensionBody)).encode result.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(namedBoth outerPair (.ex 9 extensionBody)).encode,guard12.encode]
    have hp : Context Γ (namedBoth outerPair (.ex 9 extensionBody)).encode := .head _ _
    have hg : Context Γ guard12.encode := .hypothesis (by simp [Γ])
    have hp' : Context Γ (both outerPair.encode (existsCode 9 extensionBody.encode)) := by
      simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
    have hg' : Context Γ (both retained.encode (both relocatedBody.encode innerPair.encode)) := by
      simpa [guard12, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
    have hguard : Context Γ guard9.encode := by
      simpa [guard9, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
        Context.conjunctionIntro (Context.conjunctionLeft hg')
          (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight hg'))
            (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight hg')) (Context.conjunctionLeft hp')))
    exact .mp (Context.conjunctionRight hp') (.mp hguard (.closed h9))
  have h12 := guarded_exists_left 12 guard12.encode (namedBoth outerPair (.ex 9 extensionBody)).encode result.encode
    (free_vacuity 12 guard12 (by decide)) (free_vacuity 12 result (by decide)) h12point
  have h11point : KDerivation (imp guard11.encode
      (imp (namedBoth innerPair (.ex 12 (namedBoth outerPair (.ex 9 extensionBody)))).encode result.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(namedBoth innerPair (.ex 12 (namedBoth outerPair (.ex 9 extensionBody)))).encode,guard11.encode]
    have hp : Context Γ (namedBoth innerPair (.ex 12 (namedBoth outerPair (.ex 9 extensionBody)))).encode := .head _ _
    have hg : Context Γ guard11.encode := .hypothesis (by simp [Γ])
    have hp' : Context Γ (both innerPair.encode (existsCode 12 (namedBoth outerPair (.ex 9 extensionBody)).encode)) := by
      simpa [namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hp
    have hg' : Context Γ (both retained.encode relocatedBody.encode) := by
      simpa [guard11, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
    have hguard : Context Γ guard12.encode := by
      simpa [guard12, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
        Context.conjunctionIntro (Context.conjunctionLeft hg')
          (Context.conjunctionIntro (Context.conjunctionRight hg') (Context.conjunctionLeft hp'))
    exact .mp (Context.conjunctionRight hp') (.mp hguard (.closed h12))
  have h11 := guarded_exists_left 11 guard11.encode
    (namedBoth innerPair (.ex 12 (namedBoth outerPair (.ex 9 extensionBody)))).encode result.encode
    (free_vacuity 11 guard11 (by decide)) (free_vacuity 11 result (by decide)) h11point
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [newStatement.encode,relocatedBody.encode,retained.encode]
  have hn : Context Γ newStatement.encode := .head _ _
  have hs : Context Γ relocatedBody.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard11.encode := by
    simpa [guard11, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hr hs
  have hn' : Context Γ (existsCode 11 (namedBoth innerPair (.ex 12 (namedBoth outerPair (.ex 9 extensionBody)))).encode) := by
    simpa [new_statement_expanded, CompactNamed.Formula.encode] using hn
  exact .mp hn' (.mp hg (.closed h11))

theorem selected_adjoin_closed_certificate : theoremCode (certificate selected_adjoin_closed) =
    imp retained.encode (imp relocatedBody.encode (imp newStatement.encode result.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputInsideAdjoinClosed

#print axioms PASoundness.PAtoCompactProductOutputInsideAdjoinClosed.at_graph
#print axioms PASoundness.PAtoCompactProductOutputInsideAdjoinClosed.selected_adjoin_closed
#print axioms PASoundness.PAtoCompactProductOutputInsideAdjoinClosed.selected_adjoin_closed_certificate
