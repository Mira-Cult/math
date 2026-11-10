import PASoundness.PAtoCompactProductOutputGraphToPath
import PASoundness.PAtoCompactProductOutputPathToGraph

/-! Under one selected point, successor, old invariant, adjunction, and the
selected and retained triple facts, assemble both directions of the guarded
partial invariant for the new graph labelled 9. Packaging graph 9 into an
existential over graph 58 requires a separate capture-safe alpha argument:
9 is also a bound name in the path payload. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputAdjoinInvariant9

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputInsideSelected
open PASoundness.PAtoCompactProductOutputOutsideStep PASoundness.PAtoCompactProductOutputTripleNoGarbage
open PASoundness.PAtoCompactProductOutputTripleExtension PASoundness.PAtoCompactProductOutputSameSourceTriple
open PASoundness.PAtoCompactProductOutputGraphToPath PASoundness.PAtoCompactProductOutputPathToGraph

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def jointGuard : Formula := namedBoth relocatedBody (namedBoth (namedSuccessor 74 59 76)
  (namedBoth PAtoCompactProductOutputTripleNoGarbage.guard
    (namedBoth oldInvariant (namedBoth selectedTriple newRetained))))
def point : Formula := .imp endpointGuard (namedBoth
  (.imp PAtoCompactProductOutputGraphToPath.newTriple pathAt)
  (.imp pathAt PAtoCompactProductOutputGraphToPath.newTriple))
def nextInvariant9 : Formula := .all 56 (.all 57 (.all 60 point))

theorem next_invariant_shape : nextInvariant9 = replace 58 9 partialInvariant := by decide

/-- The two guarded coverage directions for a fixed endpoint query. -/
def pointwise_invariant : KDerivation (imp jointGuard.encode point.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [endpointGuard.encode,jointGuard.encode]
  have he : Context Γ endpointGuard.encode := .head _ _
  have hj : Context Γ jointGuard.encode := .hypothesis (by simp [Γ])
  have hj' : Context Γ (both relocatedBody.encode (both (successorCode 74 59 76)
      (both PAtoCompactProductOutputTripleNoGarbage.guard.encode
        (both oldInvariant.encode (both selectedTriple.encode newRetained.encode))))) := by
    simpa [jointGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using hj
  have hs := Context.conjunctionLeft hj'
  have hsucc := Context.conjunctionLeft (Context.conjunctionRight hj')
  have hng := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hj'))
  have ho := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hj')))
  have ht := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hj'))))
  have hr := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hj'))))
  have hfguard : Context Γ PAtoCompactProductOutputGraphToPath.stepGuard.encode := by
    simpa [PAtoCompactProductOutputGraphToPath.stepGuard, namedSuccessor, namedSuccessorBody, successorCode,
      namedBoth, namedEither, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using
        Context.conjunctionIntro hs (Context.conjunctionIntro hsucc (Context.conjunctionIntro hng ho))
  have hbguard : Context Γ coverageGuard.encode := by
    simpa [coverageGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using
        Context.conjunctionIntro hs (Context.conjunctionIntro hsucc (Context.conjunctionIntro ho (Context.conjunctionIntro ht hr)))
  have hf := Context.mp he (Context.mp hfguard (.closed graph_to_path))
  have hb := Context.mp he (Context.mp hbguard (.closed path_to_graph))
  simpa [point, PAtoCompactProductOutputGraphToPath.newTriple,
    PAtoCompactProductOutputPathToGraph.newTriple, namedBoth, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, both, neg] using Context.conjunctionIntro hf hb

/-- The full query-quantified invariant for this free graph label 9. -/
def adjoin_invariant9 : KDerivation (imp jointGuard.encode nextInvariant9.encode) := by
  let Γ := [jointGuard.encode]
  have h : Context Γ point.encode := .mp (.head _ _) (.closed pointwise_invariant)
  have hv (v : Nat) (fresh : v ∉ jointGuard.free) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    have he : q = jointGuard.encode := by simpa [Γ] using hq
    subst q
    exact free_vacuity v jointGuard fresh
  have hall := Context.generalize 56 (hv 56 (by decide))
    (Context.generalize 57 (hv 57 (by decide))
      (Context.generalize 60 (hv 60 (by decide)) h))
  apply Context.closeEmpty
  apply Context.deduction
  simpa [nextInvariant9, CompactNamed.Formula.encode] using hall

theorem adjoin_invariant9_certificate : theoremCode (certificate adjoin_invariant9) =
    imp jointGuard.encode nextInvariant9.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputAdjoinInvariant9

#print axioms PASoundness.PAtoCompactProductOutputAdjoinInvariant9.pointwise_invariant
#print axioms PASoundness.PAtoCompactProductOutputAdjoinInvariant9.adjoin_invariant9
#print axioms PASoundness.PAtoCompactProductOutputAdjoinInvariant9.adjoin_invariant9_certificate
