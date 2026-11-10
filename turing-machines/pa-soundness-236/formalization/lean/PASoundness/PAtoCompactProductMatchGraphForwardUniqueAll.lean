import PASoundness.PAtoCompactProductMatchGraphForwardUnique

/-! Quantified guarded forward uniqueness for a supplied product-match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactProductMatchGraphOrder PASoundness.PAtoCompactProductMatchGraphForwardUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def forwardUniqueAll : Formula := .all 32 (.all 35 (.all 55 (.imp endpoints (.equal 55 35))))

def forward_unique_all : KDerivation (imp actualMatch.encode forwardUniqueAll.encode) := by
  have h : Context [actualMatch.encode] (imp endpoints.encode (equal 55 35)) :=
    Context.mp (.head _ _) (.closed forward_unique)
  have hv (v : Nat) (fresh : v ∉ actualMatch.names) :
      ∀ f, f ∈ [actualMatch.encode] → KDerivation (imp f (allCode v f)) := by
    intro f hf
    have he : f = actualMatch.encode := by simpa using hf
    subst f
    exact actualMatch.vacuity v fresh
  have hall := Context.generalize 32 (hv 32 (by decide))
    (Context.generalize 35 (hv 35 (by decide))
      (Context.generalize 55 (hv 55 (by decide)) h))
  apply Context.closeEmpty
  apply Context.deduction
  simpa [forwardUniqueAll, Formula.encode] using hall

theorem forward_unique_all_certificate : theoremCode (certificate forward_unique_all) =
    imp actualMatch.encode forwardUniqueAll.encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll

#print axioms PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll.forward_unique_all
#print axioms PASoundness.PAtoCompactProductMatchGraphForwardUniqueAll.forward_unique_all_certificate
