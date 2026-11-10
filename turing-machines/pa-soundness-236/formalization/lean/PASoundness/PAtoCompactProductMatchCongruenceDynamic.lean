import PASoundness.PAtoCompactProductMatchAliasSafe
import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-! Alias-safe arbitrary-label product congruence under an explicit source
domain guard. Each relation instance is transported through a fresh common
allocator, and no operand-value inequality is assumed. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCongruenceDynamic

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMulBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactProductMatchInstantiateName PASoundness.PAtoCompactProductMatchAliasSafe

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Fixed finite K proof data for arbitrary, possibly aliased, name labels.
The six bounds keep the caller's names outside its private allocator block. -/
noncomputable def guarded_product_congruence (b x y z u v w : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hu : u < b + 2) (hv : v < b + 2) (hw : w < b + 2) :
    KDerivation (frame b x y z u v w).encode := by
  let c := chosenBase x y z u v w
  have hx' : x < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hy' : y < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hz' : z < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hu' : u < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hv' : v < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hw' : w < c + 2 := by dsimp [c, chosenBase, placeholder]; omega
  have hs := (mulAt_base_alpha b c x y z hx hy hz hx' hy' hz').forward
  have ht := (mulAt_base_alpha b c u v w hu hv hw hu' hv' hw').forward
  have he₁ := (equivAt_base_alpha b c x u hx hu hx' hu').forward
  have he₂ := (equivAt_base_alpha b c y v hy hv hy' hv').forward
  have hd := domainAt_transport b c z (by omega) (by omega)
  have hr := (equivAt_base_alpha c b z w hz' hw' hz hw).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt b z).encode,(equivAt b y v).encode,(equivAt b x u).encode,
    (mulAt b u v w).encode,(mulAt b x y z).encode]
  have hd₀ : Context Γ (domainAt b z).encode := .head _ _
  have he₂₀ : Context Γ (equivAt b y v).encode := .hypothesis (by simp [Γ])
  have he₁₀ : Context Γ (equivAt b x u).encode := .hypothesis (by simp [Γ])
  have ht₀ : Context Γ (mulAt b u v w).encode := .hypothesis (by simp [Γ])
  have hs₀ : Context Γ (mulAt b x y z).encode := .hypothesis (by simp [Γ])
  have hcore : KDerivation (imp (mulAt c x y z).encode (imp (mulAt c u v w).encode
      (imp (equivAt c x u).encode (imp (equivAt c y v).encode
        (imp (domainAt c z).encode (equivAt c z w).encode))))) := by
    simpa [c, frame, Formula.encode] using alias_safe_congruence x y z u v w
  have h := Context.mp (Context.mp hd₀ (.closed hd)) (Context.mp (Context.mp he₂₀ (.closed he₂))
    (Context.mp (Context.mp he₁₀ (.closed he₁)) (Context.mp (Context.mp ht₀ (.closed ht))
      (Context.mp (Context.mp hs₀ (.closed hs)) (.closed hcore)))))
  simpa [Γ, frame, Formula.encode] using Context.mp h (.closed hr)

theorem guarded_product_congruence_certificate (b x y z u v w : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2)
    (hu : u < b + 2) (hv : v < b + 2) (hw : w < b + 2) :
    theoremCode (certificate (guarded_product_congruence b x y z u v w hx hy hz hu hv hw)) =
      (frame b x y z u v w).encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchCongruenceDynamic

#print axioms PASoundness.PAtoCompactProductMatchCongruenceDynamic.guarded_product_congruence
#print axioms PASoundness.PAtoCompactProductMatchCongruenceDynamic.guarded_product_congruence_certificate
