import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactProductCardinality
import PASoundness.PAtoCompactMultiplicationComplete

/-! Standard-ordinal calibration of a proposed product relation. This is not a
K derivation, quotient congruence, or translation of PA multiplication. -/
namespace PASoundness.PAtoCompactMultiplicationSound
open PASoundness.CompactNamed PASoundness.CompactMatrix PASoundness.HFCoding
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductCardinality
open PASoundness.PAtoCompactMultiplicationComplete

/-- If the proposed product formula holds of standard finite ordinal codes,
their indices satisfy the multiplication equation. The graph's existence is
part of the premise; no product graph is constructed here. -/
theorem ordinal_product_sound (m n k : Nat) (ρ : Environment)
    (h0 : ρ 0 = (ordinal m).code) (h1 : ρ 1 = (ordinal n).code)
    (h2 : ρ 2 = (ordinal k).code) (h : productFormula.Realize ρ) :
    k = m * n := by
  have hp := (product_realize_iff ρ).mp h
  rw [h0, h1, h2] at hp
  obtain ⟨g, hf, hr, _⟩ := hp
  apply ordinal_product_bijection_cardinality m n k (tripleRel g) hf
  intro c hc
  obtain ⟨a, b, ha, hb, hab, hu⟩ := hr c hc
  refine ⟨a, ha, b, hb, hab, ?_⟩
  intro a' ha' b' hb' hrel
  exact hu a' b' ha' hb' hrel

/-- The same direction for the literal compact encoding, using its standard
HF encoding correspondence. -/
theorem encoded_ordinal_product_sound (m n k : Nat) (ρ : Environment)
    (h0 : ρ 0 = (ordinal m).code) (h1 : ρ 1 = (ordinal n).code)
    (h2 : ρ 2 = (ordinal k).code)
    (h : (CompactMatrix.decode productFormula.encode).Realize ρ) :
    k = m * n :=
  ordinal_product_sound m n k ρ h0 h1 h2 ((Formula.encode_realize _ _).mp h)

/-- On standard finite ordinal inputs the literal encoding has exactly the
ordinary multiplication truth value. The reverse direction constructs its
graph using standard-HF finite assembly, not a K derivation. -/
theorem encoded_ordinal_product_iff (m n k : Nat) (ρ : Environment)
    (h0 : ρ 0 = (ordinal m).code) (h1 : ρ 1 = (ordinal n).code)
    (h2 : ρ 2 = (ordinal k).code) :
    (CompactMatrix.decode productFormula.encode).Realize ρ ↔ k = m*n := by
  constructor
  · exact encoded_ordinal_product_sound m n k ρ h0 h1 h2
  · intro hk
    subst k
    apply (Formula.encode_realize _ _).mpr
    apply (product_realize_iff _).mpr
    rw [h0,h1,h2]
    exact ordinal_product_semantics m n

end PASoundness.PAtoCompactMultiplicationSound

#print axioms PASoundness.PAtoCompactMultiplicationSound.ordinal_product_sound
#print axioms PASoundness.PAtoCompactMultiplicationSound.encoded_ordinal_product_sound
#print axioms PASoundness.PAtoCompactMultiplicationSound.encoded_ordinal_product_iff
