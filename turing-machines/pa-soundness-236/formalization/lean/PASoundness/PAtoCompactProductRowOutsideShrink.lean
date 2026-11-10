import PASoundness.PAtoCompactProductRowOutsidePrefix
import PASoundness.PAtoCompactMultiplicationRowPrefixTransport

/-! Outside-index transport for a literal product-row witness. If the new
prefix point is outside the row index set, every witness using the successor
prefix already witnesses the old prefix. This constructs finite K proof data;
it does not construct a row graph or establish multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductRowOutsideShrink
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactProductRowOutsidePrefix
open PASoundness.PAtoCompactMultiplicationRowPrefixTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def H : Formula := namedBoth (namedSuccessor 0 1 2) (Formula.member 31 0).not

private def body_shrink : KDerivation
    (imp H.encode (imp (rowBody 1).encode (rowBody 0).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(rowBody 1).encode, H.encode]
  have hb : Context Γ (rowBody 1).encode := .head _ _
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 0 1 2) := by
    simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using (Context.conjunctionLeft hh)
  have hn : Context Γ (neg (member 31 0)) := by
    simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using (Context.conjunctionRight hh)
  have hc : Context Γ (both (imp (both (member 1 3) (member 31 3))
      (both (member 0 3) (member 31 3)))
      (imp (both (member 0 3) (member 31 3))
        (both (member 1 3) (member 31 3)))) :=
    .mp hn (.mp hs (.closed outside_intersection_point))
  change Context Γ (both (member 1 3) (both (member 31 3)
    (both (graphFormula 6 3 4).encode
      (both (pairFormula 5 30 3).encode (pairFormula 9 5 4).encode)))) at hb
  change Context Γ (both (member 0 3) (both (member 31 3)
    (both (graphFormula 6 3 4).encode
      (both (pairFormula 5 30 3).encode (pairFormula 9 5 4).encode))))
  have hboth : Context Γ (both (member 0 3) (member 31 3)) :=
    .mp (Context.conjunctionIntro (Context.conjunctionLeft hb)
      (Context.conjunctionLeft (Context.conjunctionRight hb))) (Context.conjunctionLeft hc)
  exact Context.conjunctionIntro (Context.conjunctionLeft hboth) (Context.conjunctionRight hb)

/-- Under successor extension and nonmembership of the adjoined point in the
row domain, every new-prefix row witness is already an old-prefix witness. -/
def outside_row_witness_shrink : KDerivation
    (imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (imp (rowWitness 1).encode (rowWitness 0).encode))) := by
  have hs5 := conditionalExistsCongr 5 (H.vacuity 5 (by decide)) body_shrink
  have hs4 := conditionalExistsCongr 4 (H.vacuity 4 (by decide)) hs5
  have hs3 := conditionalExistsCongr 3 (H.vacuity 3 (by decide)) hs4
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 31 0),successorCode 0 1 2]
  have hn : Context Γ (neg (member 31 0)) := .head _ _
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  have hh : Context Γ H.encode := by
    simpa [H,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
      Formula.not,successorCode,both,neg,either] using Context.conjunctionIntro hs hn
  have hout := Context.mp hh (.closed hs3)
  simpa [rowWitness, Formula.encode] using hout

theorem outside_row_witness_shrink_certificate :
    theoremCode (certificate outside_row_witness_shrink) =
      imp (successorCode 0 1 2) (imp (neg (member 31 0))
        (imp (rowWitness 1).encode (rowWitness 0).encode)) :=
  certificate_correct outside_row_witness_shrink
end PASoundness.PAtoCompactProductRowOutsideShrink
#print axioms PASoundness.PAtoCompactProductRowOutsideShrink.outside_row_witness_shrink
#print axioms PASoundness.PAtoCompactProductRowOutsideShrink.outside_row_witness_shrink_certificate
