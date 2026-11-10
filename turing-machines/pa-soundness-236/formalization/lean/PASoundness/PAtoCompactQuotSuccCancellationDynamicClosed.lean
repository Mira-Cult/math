import PASoundness.PAtoCompactQuotSuccFixedFrameClosed
import PASoundness.PAtoCompactQuotSuccCancellationDynamicFromAliases

/-! Dynamic quotient-successor cancellation as finite K proof data. The fixed
capture-safe proof is transported to arbitrary allocator blocks; operand names
may coincide. No semantic soundness or PA proof translation is used here. -/
namespace PASoundness.PAtoCompactQuotSuccCancellationDynamicClosed
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate
open PASoundness.PAtoCompactQuotSuccCancellationDynamicFromAliases
open PASoundness.PAtoCompactQuotSuccFixedFrameClosed
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- If two quotient-successor outputs are equivalent, their inputs are
equivalent. All four names may alias; all must lie below the private block. -/
noncomputable def quotient_successor_cancellation
    (b a c p q : Nat) (ha : a < b+2) (hc : c < b+2)
    (hp : p < b+2) (hq : q < b+2) :
    KDerivation (imp (succAt b a p).encode (imp (succAt b c q).encode
      (imp (equivAt b p q).encode (equivAt b a c).encode))) := by
  have h := dynamic_from_aliases 100 b a c p q (by omega) ha hc hp hq fixed_frame
  exact h

theorem quotient_successor_cancellation_certificate
    (b a c p q : Nat) (ha : a < b+2) (hc : c < b+2)
    (hp : p < b+2) (hq : q < b+2) :
    theoremCode (certificate (quotient_successor_cancellation b a c p q ha hc hp hq)) =
      imp (succAt b a p).encode (imp (succAt b c q).encode
        (imp (equivAt b p q).encode (equivAt b a c).encode)) := certificate_correct _
end PASoundness.PAtoCompactQuotSuccCancellationDynamicClosed

#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicClosed.quotient_successor_cancellation
#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicClosed.quotient_successor_cancellation_certificate
