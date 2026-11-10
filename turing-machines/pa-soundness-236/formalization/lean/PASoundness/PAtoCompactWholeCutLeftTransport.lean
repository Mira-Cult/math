import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactStagedEquivalenceAligned
import PASoundness.PAtoCompactDynamicTransitivityFinal
import PASoundness.PAtoCompactAdditionRightZeroSchemaFixed
import PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated

/-! Equal-cut left-endpoint transport and the resulting fixed-label zero-right
addition. These are conditional finite K proof-data steps; they do not select
a cut, establish its suffix is empty, or prove addition output transport. -/
namespace PASoundness.PAtoCompactWholeCutLeftTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactStagedEquivalenceAlpha
open PASoundness.PAtoCompactStagedEquivalenceAligned PASoundness.PAtoCompactDynamicTransitivityFinal
open PASoundness.PAtoCompactZeroBaseTransport PASoundness.PAtoCompactAdditionRightZeroSchemaFixed
open PASoundness.PAtoCompactAdditionRightZeroSchemaAllocated
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Genuine equality of cut 33 and old output 32 transports the literal
left-to-cut isomorphism to the old output. -/
def left_equivalent_to_old_output : KDerivation
    (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode)) := by
  have h := (equalityReplace 33 32
    (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33) (by decide) (by decide)).1
  have hs : replace 33 32 (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33) =
      PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32 := by decide
  simpa only [hs] using h

/-- Under a candidate guard on the first operand, the original cut equality,
a literal isomorphism from that operand to the cut, a represented isomorphism
from old output 32 to new output 8, and literal zero of the second operand,
K derives the allocated addition relation with output 8. The syntactic names
are fixed while their assigned objects may coincide. -/
def whole_cut_left_transport : KDerivation
    (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp (domainAt 100 30).encode
          (imp (equivAt 100 32 8).encode
            (imp (zeroCode 31 36) (addAt 100 30 31 8).encode))))) := by
  have hraw : rawStaged 30 32 = PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32 := by decide
  have hconv : KDerivation
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode
        (equivAt 100 30 32).encode) := by
    rw [← hraw]
    exact staged_to_allocated 30 32 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hz : KDerivation (imp (zeroCode 31 36) (zeroAt 100 31).encode) := by
    have he : (zeroAt 33 31).encode = zeroCode 31 36 := rfl
    rw [← he]
    exact zeroAt_base_forward 33 100 31 (by omega) (by omega)
  have hschema : KDerivation
      (imp (zeroAt 100 31).encode
        (imp (equivAt 100 30 8).encode (addAt 100 30 31 8).encode)) := by
    have hf := schema_of_fixed true 100 30 31 8 (by omega) (by omega) (by omega)
      (fun c hc => by simpa [frame, Formula.encode] using fixed_backward c hc)
    simpa [frame, Formula.encode] using hf
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [zeroCode 31 36, (equivAt 100 32 8).encode, (domainAt 100 30).encode,
    (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode, equal 33 32]
  have hz' : Context Γ (zeroCode 31 36) := .head _ _
  have hout : Context Γ (equivAt 100 32 8).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hleft : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode :=
    .hypothesis (by simp [Γ])
  have heq : Context Γ (equal 33 32) := .hypothesis (by simp [Γ])
  have hold : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode :=
    .mp hleft (.mp heq (.closed left_equivalent_to_old_output))
  have halloc : Context Γ (equivAt 100 30 32).encode := .mp hold (.closed hconv)
  have hnew : Context Γ (equivAt 100 30 8).encode :=
    .mp hout (.mp halloc (.mp hd (.closed (dynamic_transitivity 100 30 32 8
      (by omega) (by omega) (by omega)))))
  have hzero : Context Γ (zeroAt 100 31).encode := .mp hz' (.closed hz)
  exact .mp hnew (.mp hzero (.closed hschema))

theorem whole_cut_left_transport_certificate :
    theoremCode (certificate whole_cut_left_transport) =
      imp (equal 33 32)
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
          (imp (domainAt 100 30).encode
            (imp (equivAt 100 32 8).encode
              (imp (zeroCode 31 36) (addAt 100 30 31 8).encode)))) :=
  certificate_correct whole_cut_left_transport

end PASoundness.PAtoCompactWholeCutLeftTransport

#print axioms PASoundness.PAtoCompactWholeCutLeftTransport.left_equivalent_to_old_output
#print axioms PASoundness.PAtoCompactWholeCutLeftTransport.whole_cut_left_transport
#print axioms PASoundness.PAtoCompactWholeCutLeftTransport.whole_cut_left_transport_certificate
