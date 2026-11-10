import PASoundness.PAtoCompactProductRowPrefixForward
import PASoundness.PAtoCompactProductRowOutsideShrink

/-! The old and successor-prefix row witness expressions agree when the
added prefix point is outside the row domain. This is a K formula-transport
lemma; it makes no claim that a row graph exists or that pair objects are
extensionally unique. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductRowOutsideEquivalent
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationRowPrefixTransport
open PASoundness.PAtoCompactProductRowPrefixForward PASoundness.PAtoCompactProductRowOutsideShrink
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- No new literal row witness appears if the added point is outside the
row's index domain. All nested pair witnesses remain existential. -/
def outside_row_witness_equivalent : KDerivation
    (imp (successorCode 0 1 2) (imp (neg (member 31 0))
      (both (imp (rowWitness 0).encode (rowWitness 1).encode)
        (imp (rowWitness 1).encode (rowWitness 0).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 31 0),successorCode 0 1 2]
  have hn : Context Γ (neg (member 31 0)) := .head _ _
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  exact Context.conjunctionIntro (.mp hs (.closed row_forward))
    (.mp hn (.mp hs (.closed outside_row_witness_shrink)))

theorem outside_row_witness_equivalent_certificate :
    theoremCode (certificate outside_row_witness_equivalent) =
      imp (successorCode 0 1 2) (imp (neg (member 31 0))
        (both (imp (rowWitness 0).encode (rowWitness 1).encode)
          (imp (rowWitness 1).encode (rowWitness 0).encode))) :=
  certificate_correct outside_row_witness_equivalent
end PASoundness.PAtoCompactProductRowOutsideEquivalent
#print axioms PASoundness.PAtoCompactProductRowOutsideEquivalent.outside_row_witness_equivalent
#print axioms PASoundness.PAtoCompactProductRowOutsideEquivalent.outside_row_witness_equivalent_certificate
