import PASoundness.PAtoCompactProductMatchCongruenceDynamic

/-! Multiplication operation congruence at independent allocator bases,
retaining the source-output domain guard as a literal K antecedent. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchOperationGuarded

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMulBaseMultiAlpha
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactProductMatchInstantiateName PASoundness.PAtoCompactProductMatchCongruenceDynamic

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Two matching product relations yield equivalent outputs when the source
output belongs to the candidate domain and both factors are equivalent. -/
noncomputable def operation_guarded (b c p q e f : Nat)
    (hp : p < b + 2) (hq : q < c + 2)
    (hb : b + 1 < e + 2) (hc : c + 1 < e + 2)
    (hpf : p < f + 2) (hqf : q < f + 2) : KDerivation
    (imp (domainAt b p).encode (imp (equivAt e b c).encode
      (imp (equivAt e (b+1) (c+1)).encode (imp (mulAt b b (b+1) p).encode
        (imp (mulAt c c (c+1) q).encode (equivAt f p q).encode))))) := by
  let k := b + c + p + q + e + f + 100
  have hb' : b < k + 2 := by dsimp [k]; omega
  have hb₁' : b + 1 < k + 2 := by dsimp [k]; omega
  have hc' : c < k + 2 := by dsimp [k]; omega
  have hc₁' : c + 1 < k + 2 := by dsimp [k]; omega
  have hp' : p < k + 2 := by dsimp [k]; omega
  have hq' : q < k + 2 := by dsimp [k]; omega
  have hE₁ := (equivAt_base_alpha e k b c (by omega) (by omega) hb' hc').forward
  have hE₂ := (equivAt_base_alpha e k (b+1) (c+1) hb hc hb₁' hc₁').forward
  have hM₁ := (mulAt_base_alpha b k b (b+1) p (by omega) (by omega) hp hb' hb₁' hp').forward
  have hM₂ := (mulAt_base_alpha c k c (c+1) q (by omega) (by omega) hq hc' hc₁' hq').forward
  have hD := domainAt_transport b k p (by omega) (by omega)
  have hR := (equivAt_base_alpha k f p q hp' hq' hpf hqf).forward
  have hcore : KDerivation (imp (mulAt k b (b+1) p).encode
      (imp (mulAt k c (c+1) q).encode (imp (equivAt k b c).encode
        (imp (equivAt k (b+1) (c+1)).encode
          (imp (domainAt k p).encode (equivAt k p q).encode))))) := by
    simpa [frame, Formula.encode] using guarded_product_congruence k b (b+1) p c (c+1) q
      hb' hb₁' hp' hc' hc₁' hq'
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(mulAt c c (c+1) q).encode,(mulAt b b (b+1) p).encode,
    (equivAt e (b+1) (c+1)).encode,(equivAt e b c).encode,(domainAt b p).encode]
  have hm₂ : Context Γ (mulAt c c (c+1) q).encode := .head _ _
  have hm₁ : Context Γ (mulAt b b (b+1) p).encode := .hypothesis (by simp [Γ])
  have he₂ : Context Γ (equivAt e (b+1) (c+1)).encode := .hypothesis (by simp [Γ])
  have he₁ : Context Γ (equivAt e b c).encode := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt b p).encode := .hypothesis (by simp [Γ])
  have hout := Context.mp (Context.mp hd (.closed hD)) (Context.mp (Context.mp he₂ (.closed hE₂))
    (Context.mp (Context.mp he₁ (.closed hE₁)) (Context.mp (Context.mp hm₂ (.closed hM₂))
      (Context.mp (Context.mp hm₁ (.closed hM₁)) (.closed hcore)))))
  simpa [Γ] using Context.mp hout (.closed hR)

theorem operation_guarded_certificate (b c p q e f : Nat)
    (hp : p < b + 2) (hq : q < c + 2)
    (hb : b + 1 < e + 2) (hc : c + 1 < e + 2)
    (hpf : p < f + 2) (hqf : q < f + 2) :
    theoremCode (certificate (operation_guarded b c p q e f hp hq hb hc hpf hqf)) =
      imp (domainAt b p).encode (imp (equivAt e b c).encode
        (imp (equivAt e (b+1) (c+1)).encode (imp (mulAt b b (b+1) p).encode
          (imp (mulAt c c (c+1) q).encode (equivAt f p q).encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchOperationGuarded

#print axioms PASoundness.PAtoCompactProductMatchOperationGuarded.operation_guarded
#print axioms PASoundness.PAtoCompactProductMatchOperationGuarded.operation_guarded_certificate
