import PASoundness.PAtoCompactQuotSuccCancelFreshened
import PASoundness.PAtoCompactSuccAliasFixedAlphaBridge
import PASoundness.PAtoCompactCancellationEquivAlpha100
import PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate

/-! Close the fixed allocated quotient-successor cancellation frame by composing
the capture-safe fixed proof with separately checked successor and equivalence
alpha bridges. The four labels are distinct; their values may alias. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccFixedFrameClosed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactQuotSuccWitnessFresh
open PASoundness.PAtoCompactQuotSuccCancelFreshened PASoundness.PAtoCompactCancellationGuardInputs
open PASoundness.PAtoCompactSuccAliasFixedAlphaBridge PASoundness.PAtoCompactCancellationEquivAlpha100
open PASoundness.PAtoCompactQuotSuccCancellationDynamicInstantiate
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Fixed allocated cancellation, with no supplied K proofs or endpoint guards. -/
def fixed_frame : KDerivation (frame 100 40 42 41 43).encode := by
  change KDerivation (imp (succAt 100 40 41).encode
    (imp (succAt 100 42 43).encode
      (imp (equivAt 100 41 43).encode (equivAt 100 40 42).encode)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt 100 41 43).encode, (succAt 100 42 43).encode, (succAt 100 40 41).encode]
  have he : Context Γ (equivAt 100 41 43).encode := Context.head _ _
  have hs2 : Context Γ (succAt 100 42 43).encode := .hypothesis (by simp [Γ])
  have hs1 : Context Γ (succAt 100 40 41).encode := .hypothesis (by simp [Γ])
  have ha1 : Context Γ firstAliases.encode := .mp hs1 (.closed first_alpha.backward)
  have ha2 : Context Γ secondAliases.encode := .mp hs2 (.closed second_alpha.backward)
  have he' : Context Γ edge41_43.encode := .mp he (.closed output_alpha.2)
  have hi : Context Γ inputEquivalent.encode :=
    .mp he' (.mp ha2 (.mp ha1 (.closed fixed_quotient_cancellation)))
  exact .mp hi (.closed input_alpha.1)

theorem fixed_frame_certificate : theoremCode (certificate fixed_frame) =
    (frame 100 40 42 41 43).encode := certificate_correct _
end PASoundness.PAtoCompactQuotSuccFixedFrameClosed

#print axioms PASoundness.PAtoCompactQuotSuccFixedFrameClosed.fixed_frame
#print axioms PASoundness.PAtoCompactQuotSuccFixedFrameClosed.fixed_frame_certificate
