import PASoundness.PAtoCompactSuccRelationWitnessAlpha
import PASoundness.PAtoCompactRawSuccCongruenceDynamic
import PASoundness.PAtoCompactQuotientFourEdgePath

/-! Witness-matrix step for quotient successor congruence. It constructs
finite K proof data; the existential witness elimination is separate. -/
namespace PASoundness.PAtoCompactSuccCongruenceWitnessMatrix
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSuccRelationWitnessAlpha
open PASoundness.PAtoCompactRawSuccCongruenceDynamic PASoundness.PAtoCompactQuotientFourEdgePath

/-- Equal inputs and the two opened quotient-successor matrices yield equal
outputs. The raw witness names r,s and all operand names may alias; every
name is below the matrix allocator block. -/
def matrix_congruence (b x y p q r s : Nat)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hq : q < b+2)
    (hr : r < b+2) (hs : s < b+2) :
    KDerivation (imp (equivAt b x y).encode
      (imp (matrix b x p r).encode
        (imp (matrix b y q s).encode (equivAt b p q).encode))) := by
  have raw := raw_successor_congruence b x y r s (b+10) (b+10) hx hy hr hs
    (by omega) (by omega) (by omega) (by omega)
  have route := path b r p s q hr hp hs hq
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let E := (equivAt b x y).encode
  let A := (matrix b x p r).encode
  let B := (matrix b y q s).encode
  let Γ := [B,A,E]
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .head _ _
  have hdx : Context Γ (domainAt b x).encode := Context.conjunctionLeft ha
  have ha1 := Context.conjunctionRight ha
  have hdp : Context Γ (domainAt b p).encode := Context.conjunctionLeft ha1
  have ha2 := Context.conjunctionRight ha1
  have hdr : Context Γ (domainAt b r).encode := Context.conjunctionLeft ha2
  have ha3 := Context.conjunctionRight ha2
  have hrawr : Context Γ (namedSuccessor x r (b+10)).encode := Context.conjunctionLeft ha3
  have herp : Context Γ (equivAt b r p).encode := Context.conjunctionRight ha3
  have hdy : Context Γ (domainAt b y).encode := Context.conjunctionLeft hb
  have hb1 := Context.conjunctionRight hb
  have hb2 := Context.conjunctionRight hb1
  have hb3 := Context.conjunctionRight hb2
  have hraws : Context Γ (namedSuccessor y s (b+10)).encode := Context.conjunctionLeft hb3
  have hesq : Context Γ (equivAt b s q).encode := Context.conjunctionRight hb3
  have hers : Context Γ (equivAt b r s).encode :=
    .mp hdy (.mp hdx (.mp hraws (.mp hrawr (.mp he (.closed raw)))))
  exact .mp hesq (.mp hers (.mp herp (.mp hdp (.mp hdr (.closed route)))))

end PASoundness.PAtoCompactSuccCongruenceWitnessMatrix
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessMatrix.matrix_congruence
