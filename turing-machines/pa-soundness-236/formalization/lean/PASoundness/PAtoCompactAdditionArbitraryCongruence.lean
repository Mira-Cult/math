import PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Addition congruence under explicit candidate guards and oriented
operand equivalences, with arbitrary free labels and independent bases. -/
namespace PASoundness.PAtoCompactAdditionArbitraryCongruence

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAddBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactAdditionCongruenceInstantiate
open PASoundness.PAtoCompactAdditionCongruenceArbitraryLabels

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard (du dv dz dw p q b c x y z u v w : Nat) : Formula := namedBoth (domainAt du u)
  (namedBoth (domainAt dv v) (namedBoth (equivAt p u x) (namedBoth (equivAt q v y)
    (namedBoth (domainAt dz z) (namedBoth (domainAt dw w)
      (namedBoth (addAt b x y z) (addAt c u v w)))))))

/-- The candidate new operands and results, the two oriented operand
equivalences and the two actual additions imply equivalent results. All
six free labels and represented values may alias. -/
def addition_arbitrary_congruence (du dv dz dw p q b c e x y z u v w : Nat)
    (hdu : u < du + 32) (hdv : v < dv + 32) (hdz : z < dz + 32) (hdw : w < dw + 32)
    (hup : u < p + 2) (hxp : x < p + 2) (hvq : v < q + 2) (hyq : y < q + 2)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (huc : u < c + 2) (hvc : v < c + 2) (hwc : w < c + 2)
    (hze : z < e + 2) (hwe : w < e + 2) :
    KDerivation (imp (guard du dv dz dw p q b c x y z u v w).encode (equivAt e z w).encode) := by
  let H := highBase x y z u v w
  have hxH : x < H := by dsimp [H,highBase,temporary]; omega
  have hyH : y < H := by dsimp [H,highBase,temporary]; omega
  have hzH : z < H := by dsimp [H,highBase,temporary]; omega
  have huH : u < H := by dsimp [H,highBase,temporary]; omega
  have hvH : v < H := by dsimp [H,highBase,temporary]; omega
  have hwH : w < H := by dsimp [H,highBase,temporary]; omega
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guard du dv dz dw p q b c x y z u v w).encode]
  have hg : Context Γ (guard du dv dz dw p q b c x y z u v w).encode := .head _ _
  have hdu' : Context Γ (domainAt du u).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hdv' : Context Γ (domainAt dv v).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hep : Context Γ (equivAt p u x).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have heq : Context Γ (equivAt q v y).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdz' : Context Γ (domainAt dz z).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdw' : Context Γ (domainAt dw w).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb' : Context Γ (addAt b x y z).encode := Context.conjunctionLeft hr
  have hc' : Context Γ (addAt c u v w).encode := Context.conjunctionRight hr
  have hu' : Context Γ (domainAt H u).encode := .mp hdu' (.closed (domainAt_transport du H u hdu (by omega)))
  have hv' : Context Γ (domainAt H v).encode := .mp hdv' (.closed (domainAt_transport dv H v hdv (by omega)))
  have hz' : Context Γ (domainAt H z).encode := .mp hdz' (.closed (domainAt_transport dz H z hdz (by omega)))
  have hw' : Context Γ (domainAt H w).encode := .mp hdw' (.closed (domainAt_transport dw H w hdw (by omega)))
  have hp' := (equivAt_base_alpha p H u x hup hxp (by omega) (by omega)).forward
  have hq' := (equivAt_base_alpha q H v y hvq hyq (by omega) (by omega)).forward
  have he1 : Context Γ (equivAt H u x).encode := .mp hep (.closed hp')
  have he2 : Context Γ (equivAt H v y).encode := .mp heq (.closed hq')
  have ha1 := (addAt_base_alpha b H x y z hxb hyb hzb (by omega) (by omega) (by omega)).forward
  have ha2 := (addAt_base_alpha c H u v w huc hvc hwc (by omega) (by omega) (by omega)).forward
  have hleft : Context Γ (addAt H x y z).encode := .mp hb' (.closed ha1)
  have hright : Context Γ (addAt H u v w).encode := .mp hc' (.closed ha2)
  have hframeGuard : Context Γ (namedBoth (domainAt H u) (namedBoth (domainAt H v)
      (namedBoth (equivAt H u x) (namedBoth (equivAt H v y) (namedBoth (domainAt H z)
        (namedBoth (domainAt H w) (namedBoth (addAt H x y z) (addAt H u v w)))))))).encode :=
    Context.conjunctionIntro hu' (Context.conjunctionIntro hv' (Context.conjunctionIntro he1
      (Context.conjunctionIntro he2 (Context.conjunctionIntro hz' (Context.conjunctionIntro hw'
        (Context.conjunctionIntro hleft hright))))))
  have htarget : Context Γ (equivAt H z w).encode := by
    have hframe : Context Γ (frame H x y z u v w).encode := .closed (congruence_at_high_base x y z u v w)
    exact .mp hframeGuard hframe
  have he := (equivAt_base_alpha H e z w (by omega) (by omega) hze hwe).forward
  exact .mp htarget (.closed he)

theorem addition_arbitrary_congruence_certificate (du dv dz dw p q b c e x y z u v w : Nat)
    (hdu : u < du + 32) (hdv : v < dv + 32) (hdz : z < dz + 32) (hdw : w < dw + 32)
    (hup : u < p + 2) (hxp : x < p + 2) (hvq : v < q + 2) (hyq : y < q + 2)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (huc : u < c + 2) (hvc : v < c + 2) (hwc : w < c + 2)
    (hze : z < e + 2) (hwe : w < e + 2) :
    theoremCode (certificate (addition_arbitrary_congruence du dv dz dw p q b c e x y z u v w
      hdu hdv hdz hdw hup hxp hvq hyq hxb hyb hzb huc hvc hwc hze hwe)) =
      imp (guard du dv dz dw p q b c x y z u v w).encode (equivAt e z w).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionArbitraryCongruence

#print axioms PASoundness.PAtoCompactAdditionArbitraryCongruence.guard
#print axioms PASoundness.PAtoCompactAdditionArbitraryCongruence.addition_arbitrary_congruence
#print axioms PASoundness.PAtoCompactAdditionArbitraryCongruence.addition_arbitrary_congruence_certificate
