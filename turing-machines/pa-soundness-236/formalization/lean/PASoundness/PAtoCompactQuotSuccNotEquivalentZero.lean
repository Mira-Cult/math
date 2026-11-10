import PASoundness.PAtoCompactQuotSuccWitnessAlign
import PASoundness.PAtoCompactEquivalentZeroRenamed

/-! The literal quotient successor cannot be equivalent to an explicit zero
object. This is a finite K proof with the zero graph as an object-level
premise; no full PA interpretation or semantic soundness shortcut is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccNotEquivalentZero
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactQuotientSuccessor
open PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.PAtoCompactQuotSuccWitnessAlign PASoundness.PAtoCompactEquivalentZeroRenamed
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A literal quotient successor and a zero graph for object 8 exclude the
literal E(1,8) relation. The quotient successor's actual witness is handled
in `quotient_successor_not_zero`; no additional candidate or transitivity
premise is assumed. -/
def quotient_successor_not_equivalent_zero : KDerivation
    (imp successorFormula.encode (imp (zeroCode 8 7) (neg secondEquivalent.encode))) := by
  let S := successorFormula.encode
  let Z := zeroCode 8 7
  let E := secondEquivalent.encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,Z,S]
  have he : Context Γ E := Context.head _ _
  have hz : Context Γ Z := Context.under (Context.head [S] Z) E
  have hs : Context Γ S := Context.under (Context.under (Context.head [] S) Z) E
  have hz' : Context Γ (zeroCode 1 12) :=
    .mp he (.mp hz (.closed equivalent_zero_renamed))
  exact .mp hz' (.mp hs (.closed quotient_successor_not_zero))

theorem quotient_successor_not_equivalent_zero_certificate :
    theoremCode (certificate quotient_successor_not_equivalent_zero) =
      imp successorFormula.encode (imp (zeroCode 8 7) (neg secondEquivalent.encode)) :=
  certificate_correct quotient_successor_not_equivalent_zero

end PASoundness.PAtoCompactQuotSuccNotEquivalentZero

#print axioms PASoundness.PAtoCompactQuotSuccNotEquivalentZero.quotient_successor_not_equivalent_zero
#print axioms PASoundness.PAtoCompactQuotSuccNotEquivalentZero.quotient_successor_not_equivalent_zero_certificate
