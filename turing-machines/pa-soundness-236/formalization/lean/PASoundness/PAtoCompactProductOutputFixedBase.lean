import PASoundness.PAtoCompactProductOutputFixedDomain
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-! Transport the fixed-label relation-level output theorem from allocator
100 to any allocator whose private block is above the fixed endpoint names. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputFixedBase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMulBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactProductOutputFixedDomain

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def frame (b x y p q : Nat) : Formula := .imp (mulAt b x y p)
  (.imp (equivAt b p q) (.imp (domainAt b p) (mulAt b x y q)))

/-- Fixed factor/output labels at any admissible allocator. -/
noncomputable def fixed_base_output (b : Nat) (hb : 44 < b + 2) : KDerivation (frame b 43 44 0 42).encode := by
  have hs := (mulAt_base_alpha b 100 43 44 0 (by omega) (by omega) (by omega)
    (by decide) (by decide) (by decide)).forward
  have he := (equivAt_base_alpha b 100 0 42 (by omega) (by omega) (by decide) (by decide)).forward
  have hd := domainAt_transport b 100 0 (by omega) (by omega)
  have ht := (mulAt_base_alpha 100 b 43 44 42 (by decide) (by decide) (by decide)
    (by omega) (by omega) (by omega)).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b 0).encode,(equivAt b 0 42).encode,(mulAt b 43 44 0).encode]
  have hd0 : Context Γ (domainAt b 0).encode := .head _ _
  have he0 : Context Γ (equivAt b 0 42).encode := .hypothesis (by simp [Γ])
  have hs0 : Context Γ (mulAt b 43 44 0).encode := .hypothesis (by simp [Γ])
  have h := Context.mp (Context.mp hd0 (.closed hd))
    (Context.mp (Context.mp he0 (.closed he)) (Context.mp (Context.mp hs0 (.closed hs)) (.closed fixed_domain_output)))
  simpa [Γ, frame, CompactNamed.Formula.encode] using Context.mp h (.closed ht)

theorem fixed_base_output_certificate (b : Nat) (hb : 44 < b + 2) :
    theoremCode (certificate (fixed_base_output b hb)) = (frame b 43 44 0 42).encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputFixedBase

#print axioms PASoundness.PAtoCompactProductOutputFixedBase.fixed_base_output
#print axioms PASoundness.PAtoCompactProductOutputFixedBase.fixed_base_output_certificate
