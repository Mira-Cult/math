import PASoundness.PAtoCompactAdditionOutputFrame
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-! Transport a supplied fixed-label addition-output proof from allocator 100
to any larger allocator. This does not construct the source proof. -/
namespace PASoundness.PAtoCompactAdditionOutputFixedBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdditionOutputFrame
open PASoundness.PAtoCompactAddBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactGuardBaseTransport
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle
attribute [local irreducible] domainAt addAt equivAt

/-- The same fixed labels 30,31,32,8 are interpreted at base b. All four
domain guards and the equivalence remain explicit; values may coincide. -/
noncomputable def fixed_frame_at_base (b : Nat) (hb : 100 ≤ b)
    (h100 : KDerivation (frame 100 30 31 32 8).encode) :
    KDerivation (frame b 30 31 32 8).encode := by
  have hp : KDerivation (imp (addAt 100 30 31 32).encode
      (imp (domainAt 100 32).encode (imp (domainAt 100 8).encode
        (imp (domainAt 100 31).encode (imp (domainAt 100 30).encode
          (imp (equivAt 100 32 8).encode (addAt 100 30 31 8).encode)))))) := by
    simpa only [frame,Formula.encode] using h100
  change KDerivation (imp (addAt b 30 31 32).encode
    (imp (domainAt b 32).encode (imp (domainAt b 8).encode
      (imp (domainAt b 31).encode (imp (domainAt b 30).encode
        (imp (equivAt b 32 8).encode (addAt b 30 31 8).encode))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b 32 8).encode,(domainAt b 30).encode,(domainAt b 31).encode,
    (domainAt b 8).encode,(domainAt b 32).encode,(addAt b 30 31 32).encode]
  have he : Context Γ (equivAt b 32 8).encode := .head _ _
  have hd30 : Context Γ (domainAt b 30).encode := .hypothesis (by simp [Γ])
  have hd31 : Context Γ (domainAt b 31).encode := .hypothesis (by simp [Γ])
  have hd8 : Context Γ (domainAt b 8).encode := .hypothesis (by simp [Γ])
  have hd32 : Context Γ (domainAt b 32).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (addAt b 30 31 32).encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (addAt 100 30 31 32).encode :=
    .mp ha (.closed (addAt_base_alpha b 100 30 31 32 (by omega) (by omega) (by omega)
      (by decide) (by decide) (by decide)).forward)
  have hd32' : Context Γ (domainAt 100 32).encode :=
    .mp hd32 (.closed (domainAt_transport b 100 32 (by omega) (by decide)))
  have hd8' : Context Γ (domainAt 100 8).encode :=
    .mp hd8 (.closed (domainAt_transport b 100 8 (by omega) (by decide)))
  have hd31' : Context Γ (domainAt 100 31).encode :=
    .mp hd31 (.closed (domainAt_transport b 100 31 (by omega) (by decide)))
  have hd30' : Context Γ (domainAt 100 30).encode :=
    .mp hd30 (.closed (domainAt_transport b 100 30 (by omega) (by decide)))
  have he' : Context Γ (equivAt 100 32 8).encode :=
    .mp he (.closed (equivAt_base_alpha b 100 32 8 (by omega) (by omega)
      (by decide) (by decide)).forward)
  have ht : Context Γ (addAt 100 30 31 8).encode :=
    .mp he' (.mp hd30' (.mp hd31' (.mp hd8' (.mp hd32' (.mp ha' (.closed hp))))))
  exact .mp ht (.closed (addAt_base_alpha 100 b 30 31 8 (by decide) (by decide) (by decide)
    (by omega) (by omega) (by omega)).forward)

theorem fixed_frame_at_base_certificate (b : Nat) (hb : 100 ≤ b)
    (h100 : KDerivation (frame 100 30 31 32 8).encode) :
    theoremCode (certificate (fixed_frame_at_base b hb h100)) =
      (frame b 30 31 32 8).encode := certificate_correct _
end PASoundness.PAtoCompactAdditionOutputFixedBase

#print axioms PASoundness.PAtoCompactAdditionOutputFixedBase.fixed_frame_at_base
#print axioms PASoundness.PAtoCompactAdditionOutputFixedBase.fixed_frame_at_base_certificate
