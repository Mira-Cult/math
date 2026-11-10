import PASoundness.PAtoCompactRawSuccCongruenceRelocate
import PASoundness.PAtoCompactRawSuccCongruenceInstantiate
import PASoundness.PAtoCompactRawSuccBridge
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Candidate-relative raw successor congruence at arbitrary names and
private allocator bases. This is finite K proof data, not semantic truth. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRawSuccCongruenceDynamic
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactRawSuccBridge PASoundness.PAtoCompactEquivMultiAlpha

/-- Equivalent candidate inputs have equivalent raw successor outputs.
The raw successor test names are fresh for their operands; the four operand
names may alias. Domain and equivalence templates share base b. -/
def raw_successor_congruence (b x y s t u v : Nat)
    (hx : x < b+2) (hy : y < b+2) (hs : s < b+2) (ht : t < b+2)
    (hxu : x ≠ u) (hsu : s ≠ u) (hyv : y ≠ v) (htv : t ≠ v) :
    KDerivation (imp (equivAt b x y).encode
      (imp (namedSuccessor x s u).encode (imp (namedSuccessor y t v).encode
        (imp (domainAt b x).encode (imp (domainAt b y).encode (equivAt b s t).encode))))) := by
  let q := max (max (max (max 8 x) y) s) t + 1
  let d := max (max b q) (max u v) + 100
  let e := d + 100
  have hf := PASoundness.PAtoCompactRawSuccCongruenceRelocate.relocated d e
    (by dsimp [d]; omega) (by dsimp [e]; omega)
  have hi := PASoundness.PAtoCompactRawSuccCongruenceInstantiate.instantiate_frame d e x y s t q
    (by dsimp [q]; omega) (by dsimp [d,q]; omega) (by dsimp [e,d,q]; omega)
    (by simpa only [PASoundness.PAtoCompactRawSuccCongruenceInstantiate.frame,
      PASoundness.PAtoCompactRawSuccCongruenceRelocate.frame] using hf)
  have hE := (equivAt_base_alpha b e x y hx hy (by dsimp [e,d]; omega) (by dsimp [e,d]; omega)).forward
  have hT := (equivAt_base_alpha e b s t (by dsimp [e,d]; omega) (by dsimp [e,d]; omega) hs ht).forward
  have hX := candidate_transitive_frame b d x (by dsimp [d]; omega) (by omega) (by dsimp [d]; omega)
  have hY := candidate_transitive_frame b d y (by dsimp [d]; omega) (by omega) (by dsimp [d]; omega)
  have hS := raw_successor_alpha x s u (d+2) (by dsimp [d]; omega) hxu hsu
    (by dsimp [d]; omega) (by dsimp [d]; omega)
  have hR := raw_successor_alpha y t v (d+3) (by dsimp [d]; omega) hyv htv
    (by dsimp [d]; omega) (by dsimp [d]; omega)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let E := (equivAt b x y).encode
  let S := (namedSuccessor x s u).encode
  let T := (namedSuccessor y t v).encode
  let X := (domainAt b x).encode
  let Y := (domainAt b y).encode
  let Γ := [Y,X,T,S,E]
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hs' : Context Γ S := .hypothesis (by simp [Γ])
  have ht' : Context Γ T := .hypothesis (by simp [Γ])
  have hx' : Context Γ X := .hypothesis (by simp [Γ])
  have hy' : Context Γ Y := .head _ _
  have he' : Context Γ (equivAt e x y).encode := .mp he (.closed hE)
  have hs'' : Context Γ (namedSuccessor x s (d+2)).encode := .mp hs' (.closed hS)
  have ht'' : Context Γ (namedSuccessor y t (d+3)).encode := .mp ht' (.closed hR)
  have hx'' := Context.mp hx' (.closed hX)
  have hy'' := Context.mp hy' (.closed hY)
  have hresult : Context Γ (equivAt e s t).encode := by
    exact .mp hy'' (.mp hx'' (.mp ht'' (.mp hs'' (.mp he' (.closed hi)))))
  exact .mp hresult (.closed hT)

end PASoundness.PAtoCompactRawSuccCongruenceDynamic
#print axioms PASoundness.PAtoCompactRawSuccCongruenceDynamic.raw_successor_congruence
