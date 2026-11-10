import PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Candidate-guarded same-input addition functionality at arbitrary free
labels and independently allocated binder bases. -/
namespace PASoundness.PAtoCompactAdditionArbitraryFunctionality

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAddBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactAdditionFunctionalityInstantiate
open PASoundness.PAtoCompactAdditionFunctionalityArbitraryLabels

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard (dx dy dz dw b c x y z w : Nat) : Formula := namedBoth (domainAt dx x)
  (namedBoth (domainAt dy y) (namedBoth (domainAt dz z) (namedBoth (domainAt dw w)
    (namedBoth (addAt b x y z) (addAt c x y w)))))

/-- The four values are candidate-guarded, the two addition relations have
the same inputs, and all four free labels may alias. Each private binder base
has its explicit capture-avoidance bounds. -/
def addition_arbitrary_functionality (dx dy dz dw b c e x y z w : Nat)
    (hdx : x < dx + 32) (hdy : y < dy + 32) (hdz : z < dz + 32) (hdw : w < dw + 32)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hwc : w < c + 2)
    (hze : z < e + 2) (hwe : w < e + 2) :
    KDerivation (imp (guard dx dy dz dw b c x y z w).encode (equivAt e z w).encode) := by
  let H := highBase x y z w
  have hxH : x < H := by dsimp [H,highBase,temporary]; omega
  have hyH : y < H := by dsimp [H,highBase,temporary]; omega
  have hzH : z < H := by dsimp [H,highBase,temporary]; omega
  have hwH : w < H := by dsimp [H,highBase,temporary]; omega
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guard dx dy dz dw b c x y z w).encode]
  have hg : Context Γ (guard dx dy dz dw b c x y z w).encode := .head _ _
  have hdx' : Context Γ (domainAt dx x).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hdy' : Context Γ (domainAt dy y).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdz' : Context Γ (domainAt dz z).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdw' : Context Γ (domainAt dw w).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb' : Context Γ (addAt b x y z).encode := Context.conjunctionLeft hr
  have hc' : Context Γ (addAt c x y w).encode := Context.conjunctionRight hr
  have hx' : Context Γ (domainAt H x).encode := .mp hdx' (.closed (domainAt_transport dx H x hdx (by omega)))
  have hy' : Context Γ (domainAt H y).encode := .mp hdy' (.closed (domainAt_transport dy H y hdy (by omega)))
  have hz' : Context Γ (domainAt H z).encode := .mp hdz' (.closed (domainAt_transport dz H z hdz (by omega)))
  have hw' : Context Γ (domainAt H w).encode := .mp hdw' (.closed (domainAt_transport dw H w hdw (by omega)))
  have hab := (addAt_base_alpha b H x y z hxb hyb hzb (by omega) (by omega) (by omega)).forward
  have hac := (addAt_base_alpha c H x y w hxc hyc hwc (by omega) (by omega) (by omega)).forward
  have hleft : Context Γ (addAt H x y z).encode := .mp hb' (.closed hab)
  have hright : Context Γ (addAt H x y w).encode := .mp hc' (.closed hac)
  have hframeGuard : Context Γ (namedBoth (domainAt H x) (namedBoth (domainAt H y)
      (namedBoth (domainAt H z) (namedBoth (domainAt H w)
        (namedBoth (addAt H x y z) (addAt H x y w)))))).encode :=
    Context.conjunctionIntro hx' (Context.conjunctionIntro hy' (Context.conjunctionIntro hz'
      (Context.conjunctionIntro hw' (Context.conjunctionIntro hleft hright))))
  have htarget : Context Γ (equivAt H z w).encode := by
    have hframe : Context Γ (frame H x y z w).encode := .closed (functionality_at_high_base x y z w)
    exact .mp hframeGuard hframe
  have he := (equivAt_base_alpha H e z w (by omega) (by omega) hze hwe).forward
  exact .mp htarget (.closed he)

theorem addition_arbitrary_functionality_certificate (dx dy dz dw b c e x y z w : Nat)
    (hdx : x < dx + 32) (hdy : y < dy + 32) (hdz : z < dz + 32) (hdw : w < dw + 32)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hwc : w < c + 2)
    (hze : z < e + 2) (hwe : w < e + 2) :
    theoremCode (certificate (addition_arbitrary_functionality dx dy dz dw b c e x y z w
      hdx hdy hdz hdw hxb hyb hzb hxc hyc hwc hze hwe)) =
      imp (guard dx dy dz dw b c x y z w).encode (equivAt e z w).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionArbitraryFunctionality

#print axioms PASoundness.PAtoCompactAdditionArbitraryFunctionality.guard
#print axioms PASoundness.PAtoCompactAdditionArbitraryFunctionality.addition_arbitrary_functionality
#print axioms PASoundness.PAtoCompactAdditionArbitraryFunctionality.addition_arbitrary_functionality_certificate
