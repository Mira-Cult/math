import PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate

/-! From one supplied fixed-base K cancellation frame, obtain every allocated
frame. Operand names may alias. The fixed-base derivation remains an explicit
input; this does not establish quotient-successor cancellation on its own. -/
namespace PASoundness.PAtoCompactQuotSuccCancellationDynamicFromFixed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- One canonical derivation at a base above its four fixed operand names
suffices for any target allocator and arbitrary, possibly aliased operands. -/
noncomputable def dynamic_from_fixed
    (fixed b x y s t : Nat) (hfixed : 8 < fixed + 2)
    (hx : x < b+2) (hy : y < b+2) (hs : s < b+2) (ht : t < b+2)
    (source : KDerivation (frame fixed 0 1 7 8).encode) :
    KDerivation (frame b x y s t).encode := by
  let tmp := max (max (max (max 8 x) y) s) t + 1
  let high := max b (tmp+4) + 20
  have htmp : max (max (max (max 8 x) y) s) t < tmp := by dsimp [tmp]; omega
  have hhigh : tmp+3 < high := by dsimp [high]; omega
  have hreloc := (frame_base_alpha fixed high 0 1 7 8
    (by omega) (by omega) (by omega) hfixed
    (by omega) (by omega) (by omega) (by omega)).forward
  have hcanonical : KDerivation (frame high 0 1 7 8).encode := .mp source hreloc
  have htarget := instantiate_frame high x y s t tmp htmp hhigh hcanonical
  have hfinal := (frame_base_alpha high b x y s t
    (by omega) (by omega) (by omega) (by omega) hx hy hs ht).forward
  exact .mp htarget hfinal

theorem dynamic_from_fixed_certificate
    (fixed b x y s t : Nat) (hfixed : 8 < fixed + 2)
    (hx : x < b+2) (hy : y < b+2) (hs : s < b+2) (ht : t < b+2)
    (source : KDerivation (frame fixed 0 1 7 8).encode) :
    theoremCode (certificate (dynamic_from_fixed fixed b x y s t hfixed hx hy hs ht source)) =
      (frame b x y s t).encode := certificate_correct _
end PASoundness.PAtoCompactQuotSuccCancellationDynamicFromFixed

#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicFromFixed.dynamic_from_fixed
#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicFromFixed.dynamic_from_fixed_certificate
