import PASoundness.PAtoCompactAdditionArbitraryCongruence
import PASoundness.PAtoCompactDynamicSymmetry

/-! Reorient child graph equivalences and apply candidate-guarded addition
congruence to the two actual binary operation relations. -/
namespace PASoundness.PAtoCompactAdditionOperationGuarded

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactDynamicSymmetry

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard (e b c x y z u v w : Nat) : Formula := namedBoth (domainAt e x)
  (namedBoth (domainAt e y) (namedBoth (domainAt e u) (namedBoth (domainAt e v)
    (namedBoth (domainAt e z) (namedBoth (domainAt e w)
      (namedBoth (equivAt e x u) (namedBoth (equivAt e y v)
        (namedBoth (addAt b x y z) (addAt c u v w)))))))))

/-- Explicit candidates for both operand pairs and results allow input
equivalences in the child-functionality direction x→u and y→v. -/
def addition_operation_guarded (e b c f x y z u v w : Nat)
    (hxe : x < e + 2) (hye : y < e + 2) (hze : z < e + 2)
    (hue : u < e + 2) (hve : v < e + 2) (hwe : w < e + 2)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (huc : u < c + 2) (hvc : v < c + 2) (hwc : w < c + 2)
    (hzf : z < f + 2) (hwf : w < f + 2) :
    KDerivation (imp (guard e b c x y z u v w).encode (equivAt f z w).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guard e b c x y z u v w).encode]
  have hg : Context Γ (guard e b c x y z u v w).encode := .head _ _
  have hdx : Context Γ (domainAt e x).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hdy : Context Γ (domainAt e y).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdu : Context Γ (domainAt e u).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdv : Context Γ (domainAt e v).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdz : Context Γ (domainAt e z).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hdw : Context Γ (domainAt e w).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he1 : Context Γ (equivAt e x u).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have he2 : Context Γ (equivAt e y v).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have ha1 : Context Γ (addAt b x y z).encode := Context.conjunctionLeft hr
  have ha2 : Context Γ (addAt c u v w).encode := Context.conjunctionRight hr
  have hre1 : Context Γ (equivAt e u x).encode := .mp he1 (.mp hdx (.closed (dynamic_symmetry e x u hxe hue)))
  have hre2 : Context Γ (equivAt e v y).encode := .mp he2 (.mp hdy (.closed (dynamic_symmetry e y v hye hve)))
  have hguard : Context Γ (PASoundness.PAtoCompactAdditionArbitraryCongruence.guard
      e e e e e e b c x y z u v w).encode :=
    Context.conjunctionIntro hdu (Context.conjunctionIntro hdv (Context.conjunctionIntro hre1
      (Context.conjunctionIntro hre2 (Context.conjunctionIntro hdz (Context.conjunctionIntro hdw
        (Context.conjunctionIntro ha1 ha2))))))
  have hcong := PASoundness.PAtoCompactAdditionArbitraryCongruence.addition_arbitrary_congruence
    e e e e e e b c f x y z u v w (by omega) (by omega) (by omega) (by omega)
    hue hxe hve hye hxb hyb hzb huc hvc hwc hzf hwf
  exact .mp hguard (.closed hcong)

theorem addition_operation_guarded_certificate (e b c f x y z u v w : Nat)
    (hxe : x < e + 2) (hye : y < e + 2) (hze : z < e + 2)
    (hue : u < e + 2) (hve : v < e + 2) (hwe : w < e + 2)
    (hxb : x < b + 2) (hyb : y < b + 2) (hzb : z < b + 2)
    (huc : u < c + 2) (hvc : v < c + 2) (hwc : w < c + 2)
    (hzf : z < f + 2) (hwf : w < f + 2) :
    theoremCode (certificate (addition_operation_guarded e b c f x y z u v w
      hxe hye hze hue hve hwe hxb hyb hzb huc hvc hwc hzf hwf)) =
      imp (guard e b c x y z u v w).encode (equivAt f z w).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionOperationGuarded

#print axioms PASoundness.PAtoCompactAdditionOperationGuarded.guard
#print axioms PASoundness.PAtoCompactAdditionOperationGuarded.addition_operation_guarded
#print axioms PASoundness.PAtoCompactAdditionOperationGuarded.addition_operation_guarded_certificate
