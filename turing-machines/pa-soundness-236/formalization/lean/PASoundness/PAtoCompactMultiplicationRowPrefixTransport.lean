import PASoundness.PAtoCompactGraphAdjoinPreserve

/-! A literal K transport for proposed multiplication-row witnesses when the
index prefix is enlarged. The old and new prefix labels are 0 and 1; the row
index domain is 31, the fixed major coordinate is 30, the supplied map graph
is 6, and the prospective row edge is 9. This is only one inclusion ingredient:
it neither builds a row graph nor proves multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowPrefixTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A prospective edge 9 is `((30,3),4)` where 3 is in both
prefix k and row domain 31, and the supplied graph 6 maps 3 to 4.
Names 3,4,5 are the local row-index, value and inner-pair witnesses. -/
def rowBody (k : Nat) : Formula :=
  namedBoth (.member k 3) (namedBoth (.member 31 3)
    (namedBoth (graphFormula 6 3 4)
      (namedBoth (pairFormula 5 30 3) (pairFormula 9 5 4))))

def rowWitness (k : Nat) : Formula := .ex 3 (.ex 4 (.ex 5 (rowBody k)))

private def membershipBody : Formula := .imp (.member 0 3) (.member 1 3)
/-- Literal inclusion of prefix 0 in prefix 1. -/
def prefixInclusion : Nat := allCode 3 membershipBody.encode

private def body_step : KDerivation (imp membershipBody.encode
    (imp (rowBody 0).encode (rowBody 1).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(rowBody 0).encode, membershipBody.encode]
  have hb : Context Γ (rowBody 0).encode := .head _ _
  have hi : Context Γ membershipBody.encode := .hypothesis (by simp [Γ])
  change Context Γ (both (member 0 3) (both (member 31 3)
    (both (graphFormula 6 3 4).encode
      (both (pairFormula 5 30 3).encode (pairFormula 9 5 4).encode)))) at hb
  change Context Γ (imp (member 0 3) (member 1 3)) at hi
  change Context Γ (both (member 1 3) (both (member 31 3)
    (both (graphFormula 6 3 4).encode
      (both (pairFormula 5 30 3).encode (pairFormula 9 5 4).encode))))
  exact Context.conjunctionIntro (.mp (Context.conjunctionLeft hb) hi) (Context.conjunctionRight hb)

/-- If the old prefix is included in the new prefix, each literal row-edge
witness for the old prefix remains a witness for the new prefix. All nested
Kuratowski witnesses and the supplied graph edge are retained. -/
def row_witness_prefix_inclusion : KDerivation
    (imp prefixInclusion (imp (rowWitness 0).encode (rowWitness 1).encode)) := by
  have hv5 : KDerivation (imp membershipBody.encode (allCode 5 membershipBody.encode)) :=
    membershipBody.vacuity 5 (by decide)
  have hv4 : KDerivation (imp membershipBody.encode (allCode 4 membershipBody.encode)) :=
    membershipBody.vacuity 4 (by decide)
  have hs5 := conditionalExistsCongr 5 hv5 body_step
  have hs4 := conditionalExistsCongr 4 hv4 hs5
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(rowWitness 0).encode, prefixInclusion]
  have hi : Context Γ prefixInclusion := .hypothesis (by simp [Γ])
  have hr : Context Γ (rowWitness 0).encode := .head _ _
  have hall : Context Γ (allCode 3 (imp (existsCode 4 (existsCode 5 (rowBody 0).encode))
      (existsCode 4 (existsCode 5 (rowBody 1).encode)))) :=
    Context.allMP hi (.closed (.generalize 3 hs4))
  have hresult := exists_map_context hall hr
  exact hresult

theorem row_witness_prefix_inclusion_certificate :
    theoremCode (certificate row_witness_prefix_inclusion) =
      imp prefixInclusion (imp (rowWitness 0).encode (rowWitness 1).encode) :=
  certificate_correct row_witness_prefix_inclusion
end PASoundness.PAtoCompactMultiplicationRowPrefixTransport
#print axioms PASoundness.PAtoCompactMultiplicationRowPrefixTransport.row_witness_prefix_inclusion
#print axioms PASoundness.PAtoCompactMultiplicationRowPrefixTransport.row_witness_prefix_inclusion_certificate
