import PASoundness.PAtoCompactProductOutputAliasSafe
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-! Arbitrary-label product-output relation transport at an admissible
allocator. Factor order and explicit source domain are retained; the four
endpoint labels and represented values may alias. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputDynamic

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMulBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactProductMatchAliasSafe PASoundness.PAtoCompactProductOutputFixedBase
open PASoundness.PAtoCompactProductOutputAliasSafe

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under explicit source multiplication, output equivalence and source
domain, obtain the target multiplication at the same ordered factors. -/
noncomputable def guarded_output (b x y p q : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hp : p < b + 2) (hq : q < b + 2) :
    KDerivation (PAtoCompactProductOutputFixedBase.frame b x y p q).encode := by
  let c := chosenBase p 0 0 q x y
  have hx' : x < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hy' : y < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hp' : p < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hq' : q < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hs := (mulAt_base_alpha b c x y p hx hy hp hx' hy' hp').forward
  have he := (equivAt_base_alpha b c p q hp hq hp' hq').forward
  have hd := domainAt_transport b c p (by omega) (by omega)
  have ht := (mulAt_base_alpha c b x y q hx' hy' hq' hx hy hq).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b p).encode,(equivAt b p q).encode,(mulAt b x y p).encode]
  have hd0 : Context Γ (domainAt b p).encode := .head _ _
  have he0 : Context Γ (equivAt b p q).encode := .hypothesis (by simp [Γ])
  have hs0 : Context Γ (mulAt b x y p).encode := .hypothesis (by simp [Γ])
  have hcore : KDerivation (imp (mulAt c x y p).encode (imp (equivAt c p q).encode
      (imp (domainAt c p).encode (mulAt c x y q).encode))) := by
    simpa [c, PAtoCompactProductOutputFixedBase.frame, CompactNamed.Formula.encode] using alias_safe_output x y p q
  have hout := Context.mp (Context.mp hd0 (.closed hd))
    (Context.mp (Context.mp he0 (.closed he)) (Context.mp (Context.mp hs0 (.closed hs)) (.closed hcore)))
  simpa [Γ, PAtoCompactProductOutputFixedBase.frame, CompactNamed.Formula.encode] using Context.mp hout (.closed ht)

theorem guarded_output_certificate (b x y p q : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hp : p < b + 2) (hq : q < b + 2) :
    theoremCode (certificate (guarded_output b x y p q hx hy hp hq)) =
      (PAtoCompactProductOutputFixedBase.frame b x y p q).encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputDynamic

#print axioms PASoundness.PAtoCompactProductOutputDynamic.guarded_output
#print axioms PASoundness.PAtoCompactProductOutputDynamic.guarded_output_certificate
