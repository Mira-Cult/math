import PASoundness.PAtoCompactProductMatchBackwardCoverage
import PASoundness.PAtoCompactPartialInverseCombine

/-! Combine both quantified directions of the supplied inside-source
product-match graph extension. Pair and adjunction witnesses and the old
invariant remain literal antecedents; this module does not collect a graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchAdjoinInvariant

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPartialInverseCombine PASoundness.PAtoCompactProductMatchPartialBase
open PASoundness.PAtoCompactProductMatchOutsideStep PASoundness.PAtoCompactProductMatchInsideImage
open PASoundness.PAtoCompactProductMatchInsideAdjoinConditional
open PASoundness.PAtoCompactProductMatchForwardCoverage PASoundness.PAtoCompactProductMatchBackwardCoverage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

theorem next_shape : nextInvariant17 = .all 56 (.all 57
    (.imp (namedBoth (.member 2 56) (.member 44 57))
      (namedBoth (.imp (graphFormula 17 56 57) (namedBoth (.member 59 56) matchAt))
        (.imp (namedBoth (.member 59 56) matchAt) (graphFormula 17 56 57))))) := by decide

/-- Both coverage directions give the complete next graph invariant under
the explicit supplied context. -/
def combine : KDerivation (imp supplied.encode nextInvariant17.encode) := by
  let Q := both (member 2 56) (member 44 57)
  let T := both (member 59 56) matchAt.encode
  let G := (graphFormula 17 56 57).encode
  have hc := all2_guard_conjoin 56 57 Q (imp G T) (imp T G)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [supplied.encode]
  have hp : Context Γ supplied.encode := .head _ _
  have hf : Context Γ forwardCoverage.encode := .mp hp (.closed forward_all)
  have hb : Context Γ PASoundness.PAtoCompactProductMatchBackwardCoverage.backwardCoverage.encode :=
    .mp hp (.closed backward_all)
  have hnew : Context Γ (allCode 56 (allCode 57 (imp Q (both (imp G T) (imp T G))))) :=
    .mp hf (.mp hb (.closed hc))
  rw [next_shape]
  simpa [Q, T, G, namedBoth, Formula.not, Formula.encode, both, neg] using hnew

/-- Assemble the next invariant from the retained selected path, successor,
old graph, pair and new graph. -/
def adjoin_invariant : AdjoinInvariant := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [adjoinCode 58 16 17 18,(pairFormula 16 74 35).encode,retained.encode]
  have ha : Context Γ (adjoinCode 58 16 17 18) := .head _ _
  have hp : Context Γ (pairFormula 16 74 35).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both selectedPath.encode (both (successorCode 74 59 76) oldMatch.encode)) := by
    simpa [retained, namedSuccessor, successorCode, namedSuccessorBody,
      namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using hr
  have hpath := Context.conjunctionLeft hr'
  have hs := Context.conjunctionLeft (Context.conjunctionRight hr')
  have hold := Context.conjunctionRight (Context.conjunctionRight hr')
  have hu : Context Γ supplied.encode := by
    have h := Context.conjunctionIntro hpath (Context.conjunctionIntro hs
      (Context.conjunctionIntro hp (Context.conjunctionIntro ha hold)))
    simpa [supplied, namedSuccessor, successorCode, namedSuccessorBody, namedAdjoin,
      adjoinCode, namedBoth, namedEither, Formula.not, Formula.encode, both, neg, either] using h
  exact .mp hu (.closed combine)

theorem adjoin_invariant_certificate : theoremCode (certificate adjoin_invariant) =
    imp retained.encode (imp (pairFormula 16 74 35).encode
      (imp (adjoinCode 58 16 17 18) nextInvariant17.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchAdjoinInvariant

#print axioms PASoundness.PAtoCompactProductMatchAdjoinInvariant.combine
#print axioms PASoundness.PAtoCompactProductMatchAdjoinInvariant.adjoin_invariant
#print axioms PASoundness.PAtoCompactProductMatchAdjoinInvariant.adjoin_invariant_certificate
