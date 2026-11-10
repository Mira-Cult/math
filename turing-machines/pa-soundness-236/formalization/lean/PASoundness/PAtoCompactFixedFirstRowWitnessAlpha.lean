import PASoundness.PAtoCompactFixedFirstCoverageBase

/-! Capture-safe K alpha-conversion for the exact fixed-first row-witness
branch. The free edge name is moved to 63, and its internal row index, value
and inner-pair witnesses are renamed from 3,4,5 to 60,61,62. This does not
construct the row or prove a product graph or multiplication totality. -/
namespace PASoundness.PAtoCompactFixedFirstRowWitnessAlpha
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFixedFirstCoverageBase
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Exact old row body after changing the free edge name from 9 to 63. -/
def body0 : Formula := namedBoth (.member 0 3) (namedBoth (.member 31 3)
  (namedBoth (graphFormula 6 3 4)
    (namedBoth (pairFormula 5 30 3) (pairFormula 63 5 4))))
def body1 : Formula := replace 3 60 body0
def body2 : Formula := replace 4 61 body1
def body3 : Formula := replace 5 62 body2

/-- The freshened row predicate has the same free edge 63 and fresh
bound row-index, value and inner-pair names. -/
def freshRowWitness : Formula := .ex 60 (.ex 61 (.ex 62 body3))

theorem old_shape : replace 9 63 rowWitness = .ex 3 (.ex 4 (.ex 5 body0)) := by decide

theorem fresh_body_shape : body3 = namedBoth (.member 0 60) (namedBoth (.member 31 60)
    (namedBoth (graphFormula 6 60 61)
      (namedBoth (pairFormula 62 30 60) (pairFormula 63 62 61)))) := by decide

/-- Both directions of alpha-conversion are literal finite K proofs. -/
def row_witness_alpha :
    KDerivation (imp (replace 9 63 rowWitness).encode freshRowWitness.encode) ×
    KDerivation (imp freshRowWitness.encode (replace 9 63 rowWitness).encode) := by
  let F := Formula.ex 4 (.ex 5 body0)
  let G := Formula.ex 5 body1
  have h1 := existentialAlpha 3 60 F (by decide) (by decide) (by decide)
  have h2 := existentialAlpha 4 61 G (by decide) (by decide) (by decide)
  have h3 := existentialAlpha 5 62 body2 (by decide) (by decide) (by decide)
  have r1 : replace 3 60 F = .ex 4 (.ex 5 body1) := by decide
  have r2 : replace 4 61 G = .ex 5 body2 := by decide
  have r3 : replace 5 62 body2 = body3 := rfl
  rw [r1] at h1
  rw [r2] at h2
  rw [r3] at h3
  have h1f : KDerivation (imp (replace 9 63 rowWitness).encode
      (existsCode 60 (existsCode 4 (existsCode 5 body1.encode)))) := by
    rw [old_shape]
    simpa [F, Formula.encode] using h1.1
  have h1b : KDerivation (imp (existsCode 60 (existsCode 4 (existsCode 5 body1.encode)))
      (replace 9 63 rowWitness).encode) := by
    rw [old_shape]
    simpa [F, Formula.encode] using h1.2
  have h2f : KDerivation (imp (existsCode 60 (existsCode 4 (existsCode 5 body1.encode)))
      (existsCode 60 (existsCode 61 (existsCode 5 body2.encode)))) := by
    simpa [G, Formula.encode] using existsCongr 60 h2.1
  have h2b : KDerivation (imp (existsCode 60 (existsCode 61 (existsCode 5 body2.encode)))
      (existsCode 60 (existsCode 4 (existsCode 5 body1.encode)))) := by
    simpa [G, Formula.encode] using existsCongr 60 h2.2
  have h3f : KDerivation (imp (existsCode 60 (existsCode 61 (existsCode 5 body2.encode)))
      freshRowWitness.encode) := by
    simpa [freshRowWitness, Formula.encode] using existsCongr 60 (existsCongr 61 h3.1)
  have h3b : KDerivation (imp freshRowWitness.encode
      (existsCode 60 (existsCode 61 (existsCode 5 body2.encode)))) := by
    simpa [freshRowWitness, Formula.encode] using existsCongr 60 (existsCongr 61 h3.2)
  exact ⟨compose h1f (compose h2f h3f), compose h3b (compose h2b h1b)⟩

theorem row_witness_alpha_forward_certificate :
    theoremCode (certificate row_witness_alpha.1) =
      imp (replace 9 63 rowWitness).encode freshRowWitness.encode := certificate_correct _

theorem row_witness_alpha_reverse_certificate :
    theoremCode (certificate row_witness_alpha.2) =
      imp freshRowWitness.encode (replace 9 63 rowWitness).encode := certificate_correct _
end PASoundness.PAtoCompactFixedFirstRowWitnessAlpha
#print axioms PASoundness.PAtoCompactFixedFirstRowWitnessAlpha.row_witness_alpha
#print axioms PASoundness.PAtoCompactFixedFirstRowWitnessAlpha.row_witness_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactFixedFirstRowWitnessAlpha.row_witness_alpha_reverse_certificate
