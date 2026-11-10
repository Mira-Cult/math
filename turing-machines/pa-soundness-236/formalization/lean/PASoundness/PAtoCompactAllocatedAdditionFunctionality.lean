import PASoundness.PAtoCompactAllocatedAdditionToRaw
import PASoundness.PAtoCompactAdditionRawFunctionality
import PASoundness.PAtoCompactAddBaseMultiAlpha

/-! Candidate-guarded functionality for two allocated addition formulas,
with independently chosen fresh-enough binder bases. -/
namespace PASoundness.PAtoCompactAllocatedAdditionFunctionality

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAddBaseMultiAlpha
open PASoundness.PAtoCompactAllocatedAdditionToRaw PASoundness.PAtoCompactAdditionRawFunctionality
open PASoundness.PAtoCompactCommonSourceSpanEquivalence

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard (b c : Nat) : Formula := namedBoth (namedCandidate 28) (namedBoth (namedCandidate 1)
  (namedBoth (namedCandidate 0) (namedBoth (namedCandidate 8)
    (namedBoth (addAt b 28 1 0) (addAt c 28 1 8)))))

/-- Two allocated addition results for the same candidate operands are
isomorphic when both results are candidates. The two binder bases may differ. -/
def allocated_addition_functionality (b c : Nat) (hb : 28 < b + 2) (hc : 28 < c + 2) :
    KDerivation (imp (guard b c).encode targetEquivalent.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guard b c).encode]
  have hg : Context Γ (guard b c).encode := .head _ _
  have hc28 : Context Γ (namedCandidate 28).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hc1 : Context Γ (namedCandidate 1).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc0 : Context Γ (namedCandidate 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc8 : Context Γ (namedCandidate 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have ha1 : Context Γ (addAt b 28 1 0).encode := Context.conjunctionLeft hr
  have ha2 : Context Γ (addAt c 28 1 8).encode := Context.conjunctionRight hr
  have halpha1 := (addAt_base_alpha b 100 28 1 0 hb (by omega) (by omega)
    (by decide) (by decide) (by decide)).forward
  have halpha2 := (addAt_base_alpha c 100 28 1 8 hc (by omega) (by omega)
    (by decide) (by decide) (by decide)).forward
  have hbase1 : Context Γ (addAt 100 28 1 0).encode := .mp ha1 (.closed halpha1)
  have hbase2 : Context Γ (addAt 100 28 1 8).encode := .mp ha2 (.closed halpha2)
  have hraw1 : Context Γ PASoundness.PAtoCompactFirstAdditionCutAllocation.addition.encode :=
    .mp hbase1 (.closed first_allocated_to_raw)
  have hraw2 : Context Γ PASoundness.PAtoCompactSecondAdditionCutAllocation.addition.encode :=
    .mp hbase2 (.closed second_allocated_to_raw)
  have hrawGuard : Context Γ PASoundness.PAtoCompactAdditionRawOutputEquivalence.guard.encode :=
    Context.conjunctionIntro hc28 (Context.conjunctionIntro hc1 (Context.conjunctionIntro hc0
      (Context.conjunctionIntro hc8 (Context.conjunctionIntro hraw1 hraw2))))
  exact .mp hrawGuard (.closed raw_addition_functionality)

theorem allocated_addition_functionality_certificate (b c : Nat) (hb : 28 < b + 2) (hc : 28 < c + 2) :
    theoremCode (certificate (allocated_addition_functionality b c hb hc)) =
      imp (guard b c).encode targetEquivalent.encode := certificate_correct _

end PASoundness.PAtoCompactAllocatedAdditionFunctionality

#print axioms PASoundness.PAtoCompactAllocatedAdditionFunctionality.guard
#print axioms PASoundness.PAtoCompactAllocatedAdditionFunctionality.allocated_addition_functionality
#print axioms PASoundness.PAtoCompactAllocatedAdditionFunctionality.allocated_addition_functionality_certificate
