import PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated
import PASoundness.PAtoCompactAdditionArbitraryFunctionality

/-! Candidate-guarded addition congruence at fixed allocated labels, with
the operand equivalences oriented from the new operands to the old ones. -/
namespace PASoundness.PAtoCompactAdditionFixedOperandCongruence

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth PASoundness.PAtoCompactFirstAdditionOperandTransport.fixedGuard
  (namedBoth (domainAt 100 0) (namedBoth (domainAt 100 8)
    (namedBoth (addAt 100 28 1 0) (addAt 100 29 27 8))))

/-- The two actual additions have explicitly equivalent operands and
candidate outputs; no distinctness of represented values is assumed. -/
def fixed_operand_congruence (e : Nat) (he : 8 < e + 2) :
    KDerivation (imp guard.encode (equivAt e 0 8).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hf : Context Γ PASoundness.PAtoCompactFirstAdditionOperandTransport.fixedGuard.encode := Context.conjunctionLeft hg
  have hd29 : Context Γ (domainAt 100 29).encode := Context.conjunctionLeft hf
  have hd27 : Context Γ (domainAt 100 27).encode := Context.conjunctionLeft (Context.conjunctionRight hf)
  have hr := Context.conjunctionRight hg
  have hd0 : Context Γ (domainAt 100 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hd8 : Context Γ (domainAt 100 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hold : Context Γ (addAt 100 28 1 0).encode := Context.conjunctionLeft hr
  have hnew : Context Γ (addAt 100 29 27 8).encode := Context.conjunctionRight hr
  have htguard : Context Γ PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated.guard.encode :=
    Context.conjunctionIntro hf hold
  have haligned : Context Γ (addAt 100 29 27 0).encode :=
    .mp htguard (.closed PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated.allocated_operand_transport)
  have hguard : Context Γ (PASoundness.PAtoCompactAdditionArbitraryFunctionality.guard
      100 100 100 100 100 100 29 27 0 8).encode :=
    Context.conjunctionIntro hd29 (Context.conjunctionIntro hd27 (Context.conjunctionIntro hd0
      (Context.conjunctionIntro hd8 (Context.conjunctionIntro haligned hnew))))
  have hfun := PASoundness.PAtoCompactAdditionArbitraryFunctionality.addition_arbitrary_functionality
    100 100 100 100 100 100 e 29 27 0 8
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) he
  exact .mp hguard (.closed hfun)

theorem fixed_operand_congruence_certificate (e : Nat) (he : 8 < e + 2) :
    theoremCode (certificate (fixed_operand_congruence e he)) =
      imp guard.encode (equivAt e 0 8).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionFixedOperandCongruence

#print axioms PASoundness.PAtoCompactAdditionFixedOperandCongruence.guard
#print axioms PASoundness.PAtoCompactAdditionFixedOperandCongruence.fixed_operand_congruence
#print axioms PASoundness.PAtoCompactAdditionFixedOperandCongruence.fixed_operand_congruence_certificate
