import PASoundness.PAtoCompactAdditionCongruenceInstantiate
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Lift the fixed-label operand-congruence proof from base 100 to a
single sufficiently high common binder base. -/
namespace PASoundness.PAtoCompactAdditionCongruenceHighBase

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAddBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactAdditionCongruenceInstantiate

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def commonGuard (b : Nat) : Formula := namedBoth (domainAt b 29)
  (namedBoth (domainAt b 27) (namedBoth (equivAt b 29 28) (namedBoth (equivAt b 27 1)
    (namedBoth (domainAt b 0) (namedBoth (domainAt b 8)
      (namedBoth (addAt b 28 1 0) (addAt b 29 27 8)))))))

/-- The original fixed-label theorem holds at any base at least 100. -/
def fixed_congruence_high_base (b : Nat) (hb : 100 ≤ b) :
    KDerivation (frame b 28 1 0 29 27 8).encode := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(commonGuard b).encode]
  have hg : Context Γ (commonGuard b).encode := .head _ _
  have hd29 : Context Γ (domainAt b 29).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hd27 : Context Γ (domainAt b 27).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have heA : Context Γ (equivAt b 29 28).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have heB : Context Γ (equivAt b 27 1).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hd0 : Context Γ (domainAt b 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hd8 : Context Γ (domainAt b 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have ha1 : Context Γ (addAt b 28 1 0).encode := Context.conjunctionLeft hr
  have ha2 : Context Γ (addAt b 29 27 8).encode := Context.conjunctionRight hr
  have hc29 : Context Γ (domainAt 100 29).encode := .mp hd29 (.closed (domainAt_transport b 100 29 (by omega) (by decide)))
  have hc27 : Context Γ (domainAt 100 27).encode := .mp hd27 (.closed (domainAt_transport b 100 27 (by omega) (by decide)))
  have hc0 : Context Γ (domainAt 100 0).encode := .mp hd0 (.closed (domainAt_transport b 100 0 (by omega) (by decide)))
  have hc8 : Context Γ (domainAt 100 8).encode := .mp hd8 (.closed (domainAt_transport b 100 8 (by omega) (by decide)))
  have heA' := (equivAt_base_alpha b 100 29 28 (by omega) (by omega) (by decide) (by decide)).forward
  have heB' := (equivAt_base_alpha b 100 27 1 (by omega) (by omega) (by decide) (by decide)).forward
  have heA100 : Context Γ (equivAt 100 29 28).encode := .mp heA (.closed heA')
  have heB100 : Context Γ (equivAt 100 27 1).encode := .mp heB (.closed heB')
  have ha1' := (addAt_base_alpha b 100 28 1 0 (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide)).forward
  have ha2' := (addAt_base_alpha b 100 29 27 8 (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide)).forward
  have ha100 : Context Γ (addAt 100 28 1 0).encode := .mp ha1 (.closed ha1')
  have hb100 : Context Γ (addAt 100 29 27 8).encode := .mp ha2 (.closed ha2')
  have hf : Context Γ PASoundness.PAtoCompactFirstAdditionOperandTransport.fixedGuard.encode :=
    Context.conjunctionIntro hc29 (Context.conjunctionIntro hc27 (Context.conjunctionIntro heA100 heB100))
  have hguard : Context Γ PASoundness.PAtoCompactAdditionFixedOperandCongruence.guard.encode :=
    Context.conjunctionIntro hf (Context.conjunctionIntro hc0 (Context.conjunctionIntro hc8
      (Context.conjunctionIntro ha100 hb100)))
  have hout : Context Γ (equivAt 100 0 8).encode :=
    .mp hguard (.closed (PASoundness.PAtoCompactAdditionFixedOperandCongruence.fixed_operand_congruence 100 (by decide)))
  have hback := (equivAt_base_alpha 100 b 0 8 (by decide) (by decide) (by omega) (by omega)).forward
  exact .mp hout (.closed hback)

theorem fixed_congruence_high_base_certificate (b : Nat) (hb : 100 ≤ b) :
    theoremCode (certificate (fixed_congruence_high_base b hb)) = (frame b 28 1 0 29 27 8).encode :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionCongruenceHighBase

#print axioms PASoundness.PAtoCompactAdditionCongruenceHighBase.fixed_congruence_high_base
#print axioms PASoundness.PAtoCompactAdditionCongruenceHighBase.fixed_congruence_high_base_certificate
