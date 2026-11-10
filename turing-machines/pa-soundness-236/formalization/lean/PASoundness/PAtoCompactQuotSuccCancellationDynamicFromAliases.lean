import PASoundness.PAtoCompactQuotSuccCancellationDynamicFromFixed

/-! Move a supplied fixed-base quotient cancellation proof at fresh alias
names 40,42,41,43 to arbitrary allocated operands. This file does not prove
the fixed alias derivation; it remains an explicit finite-K input. -/
namespace PASoundness.PAtoCompactQuotSuccCancellationDynamicFromAliases
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate
open PASoundness.PAtoCompactQuotSuccCancellationDynamicFromFixed
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The fixed aliases are pairwise distinct and all above the canonical
names 0,1,7,8. Target endpoints may identify arbitrarily. -/
noncomputable def dynamic_from_aliases
    (fixed b x y s t : Nat) (hfixed : 43 < fixed)
    (hx : x < b+2) (hy : y < b+2) (hs : s < b+2) (ht : t < b+2)
    (source : KDerivation (frame fixed 40 42 41 43).encode) :
    KDerivation (frame b x y s t).encode := by
  have h1 := instantiate_name fixed 40 42 41 43 40 0 (by omega) (by omega) source
  have h1' : KDerivation (frame fixed 0 42 41 43).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h1
  have h2 := instantiate_name fixed 0 42 41 43 42 1 (by omega) (by omega) h1'
  have h2' : KDerivation (frame fixed 0 1 41 43).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h2
  have h3 := instantiate_name fixed 0 1 41 43 41 7 (by omega) (by omega) h2'
  have h3' : KDerivation (frame fixed 0 1 7 43).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h3
  have h4 := instantiate_name fixed 0 1 7 43 43 8 (by omega) (by omega) h3'
  have h4' : KDerivation (frame fixed 0 1 7 8).encode := by
    simpa only [rename, if_pos, if_neg, if_false, Nat.reduceEqDiff] using h4
  exact dynamic_from_fixed fixed b x y s t (by omega) hx hy hs ht h4'

theorem dynamic_from_aliases_certificate
    (fixed b x y s t : Nat) (hfixed : 43 < fixed)
    (hx : x < b+2) (hy : y < b+2) (hs : s < b+2) (ht : t < b+2)
    (source : KDerivation (frame fixed 40 42 41 43).encode) :
    theoremCode (certificate (dynamic_from_aliases fixed b x y s t hfixed hx hy hs ht source)) =
      (frame b x y s t).encode := certificate_correct _
end PASoundness.PAtoCompactQuotSuccCancellationDynamicFromAliases

#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicFromAliases.dynamic_from_aliases
#print axioms PASoundness.PAtoCompactQuotSuccCancellationDynamicFromAliases.dynamic_from_aliases_certificate
