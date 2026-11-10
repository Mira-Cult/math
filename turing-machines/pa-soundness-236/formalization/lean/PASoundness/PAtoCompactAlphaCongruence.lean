import PASoundness.PAtoCompactTermTranslation
import PASoundness.CompactFreshen

/-! Congruence for the named conjunction used by the arithmetic templates.
Inputs are actual K proof equivalences; this does not establish any concrete
template or term-graph equivalence. -/
namespace PASoundness.PAtoCompactAlphaCongruence

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation

/-- Named conjunction preserves finite K bidirectional equivalence. -/
def andF_congr {a a' b b' : Formula} (ha : ProofEquiv a a') (hb : ProofEquiv b b') :
    ProofEquiv (andF a b) (andF a' b') := by
  unfold andF Formula.not
  exact ProofEquiv.implication
    (ProofEquiv.implication ha (ProofEquiv.implication hb (ProofEquiv.refl .bottom)))
    (ProofEquiv.refl .bottom)

theorem andF_congr_forward_certificate {a a' b b' : Formula}
    (ha : ProofEquiv a a') (hb : ProofEquiv b b') :
    theoremCode (certificate (andF_congr ha hb).forward) =
      imp (andF a b).encode (andF a' b').encode := certificate_correct _

theorem andF_congr_backward_certificate {a a' b b' : Formula}
    (ha : ProofEquiv a a') (hb : ProofEquiv b b') :
    theoremCode (certificate (andF_congr ha hb).backward) =
      imp (andF a' b').encode (andF a b).encode := certificate_correct _

end PASoundness.PAtoCompactAlphaCongruence

#print axioms PASoundness.PAtoCompactAlphaCongruence.andF_congr
#print axioms PASoundness.PAtoCompactAlphaCongruence.andF_congr_forward_certificate
#print axioms PASoundness.PAtoCompactAlphaCongruence.andF_congr_backward_certificate
