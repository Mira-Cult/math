import PASoundness.PAtoCompactDynamicSymmetry
import PASoundness.PAtoCompactDynamicTransitivityFinal

/-! A finite-K path rule for candidate-relative quotient equivalence. All
candidate guards are explicit and operand names may coincide. -/
namespace PASoundness.PAtoCompactQuotientFourEdgePath

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactDynamicSymmetry PASoundness.PAtoCompactDynamicTransitivityFinal

/-- If s and p are candidates and s is equivalent both to p and t, while t
is equivalent to q, then p is equivalent to q. Both guards and all three
edges are actual K antecedents. No operands need be distinct. -/
def path (b s p t q : Nat)
    (hs : s < b+2) (hp : p < b+2) (ht : t < b+2) (hq : q < b+2) :
    KDerivation (imp (domainAt b s).encode (imp (domainAt b p).encode
      (imp (equivAt b s p).encode (imp (equivAt b s t).encode
        (imp (equivAt b t q).encode (equivAt b p q).encode))))) := by
  have hsym := dynamic_symmetry b s p hs hp
  have ht1 := dynamic_transitivity b p s t hp hs ht
  have ht2 := dynamic_transitivity b p t q hp ht hq
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := (domainAt b s).encode
  let P := (domainAt b p).encode
  let E := (equivAt b s p).encode
  let F := (equivAt b s t).encode
  let G := (equivAt b t q).encode
  let Γ := [G,F,E,P,S]
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hP : Context Γ P := .hypothesis (by simp [Γ])
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have hF : Context Γ F := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .head _ _
  have hrev : Context Γ (equivAt b p s).encode := .mp hE (.mp hS (.closed hsym))
  have hpt : Context Γ (equivAt b p t).encode := .mp hF (.mp hrev (.mp hP (.closed ht1)))
  exact .mp hG (.mp hpt (.mp hP (.closed ht2)))

theorem path_certificate (b s p t q : Nat)
    (hs : s < b+2) (hp : p < b+2) (ht : t < b+2) (hq : q < b+2) :
    theoremCode (certificate (path b s p t q hs hp ht hq)) =
      imp (domainAt b s).encode (imp (domainAt b p).encode
        (imp (equivAt b s p).encode (imp (equivAt b s t).encode
          (imp (equivAt b t q).encode (equivAt b p q).encode)))) :=
  certificate_correct _

end PASoundness.PAtoCompactQuotientFourEdgePath
#print axioms PASoundness.PAtoCompactQuotientFourEdgePath.path
#print axioms PASoundness.PAtoCompactQuotientFourEdgePath.path_certificate
