import PASoundness.PAtoCompactProductForwardConditional
import PASoundness.PAtoCompactMulTermTransportWitness

/-! Local endpoint witnesses for matching two product graphs. The actual
product matrix supplies a coordinate pair for an existing output and an
output for a supplied coordinate pair, retaining its literal uniqueness
clauses. No graph of matched edges is collected here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPointWitness

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductForwardConditional
open PASoundness.PAtoCompactMulTermTransportWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The product reverse clause at output name 5, before its coordinate
witnesses 3 and 4 are relocated. -/
def reverseBody : Formula := namedBoth (.member 0 3)
  (namedBoth (.member 1 4) (namedBoth (tripleFormula 3 4 5)
    (.all 7 (.all 8 (.imp (namedBoth (.member 0 7) (namedBoth (.member 1 8)
      (tripleFormula 7 8 5))) (namedBoth (.equal 7 3) (.equal 8 4)))))))

def reversePoint : Formula := .imp (.member 2 5) (.ex 3 (.ex 4 reverseBody))

theorem reverse_shape : reverseFormula = .all 5 reversePoint := by decide

/-- Source output 32 is decomposed as coordinates 30,31. Its full uniqueness
clause remains inside the existential witnesses. -/
def selectedReverseBody : Formula :=
  replace 4 31 (replace 3 30 (replace 5 32 reverseBody))

def reverse_coordinates : KDerivation
    (imp productMatrix.encode (imp (member 2 32)
      (existsCode 30 (existsCode 31 selectedReverseBody.encode)))) := by
  let F : Formula := .imp (.member 2 5) (.ex 3 (.ex 4 reverseBody))
  let W := replace 5 32 reverseBody
  have hi := universalInstance 5 32 F (by decide) (by decide) (by decide)
  have hs : replace 5 32 F = .imp (.member 2 32) (.ex 3 (.ex 4 W)) := by decide
  rw [hs] at hi
  have ha := two_exists_alpha W 3 4 30 31
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 2 32, productMatrix.encode]
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hz : Context Γ (member 2 32) := .head _ _
  change Context Γ (both forwardFormula.encode
    (both reverseFormula.encode lexFormula.encode)) at hm
  have hrev : Context Γ reverseFormula.encode :=
    Context.conjunctionLeft (Context.conjunctionRight hm)
  have hq : Context Γ (existsCode 3 (existsCode 4 W.encode)) := by
    have h := Context.mp hz (Context.mp hrev
      (by simpa [reverse_shape, reversePoint, F, Formula.encode] using Context.closed hi))
    simpa [Formula.encode] using h
  have hout := Context.mp hq (.closed ha.forward)
  simpa [selectedReverseBody, W, Formula.encode] using hout

/-- The forward witness for coordinates 30,31, before output name 5 is
renamed to 32. -/
def selectedForwardBody : Formula :=
  replace 5 32 (replace 4 31 (replace 3 30 (witnessBody 6)))

/-- Given members 30 and 31 of the corresponding factors, select a product
output 32, retaining output membership, the triple and its uniqueness clause. -/
def forward_output : KDerivation
    (imp productMatrix.encode (imp (member 0 30) (imp (member 1 31)
      (existsCode 32 selectedForwardBody.encode)))) := by
  let W := replace 4 31 (replace 3 30 (witnessBody 6))
  have h3 := universalInstance 3 30 (point3 6) (by decide) (by decide) (by decide)
  have hs3 : replace 3 30 (point3 6) =
      .imp (.member 0 30) (.all 4 (replace 3 30 (point4 6))) := by decide
  rw [hs3] at h3
  have h4 := universalInstance 4 31 (replace 3 30 (point4 6))
    (by decide) (by decide) (by decide)
  have hs4 : replace 4 31 (replace 3 30 (point4 6)) =
      .imp (.member 1 31) (.ex 5 W) := by decide
  rw [hs4] at h4
  have ha := (existentialAlpha 5 32 W (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 31, member 0 30, productMatrix.encode]
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 0 30) := .hypothesis (by simp [Γ])
  have hy : Context Γ (member 1 31) := .head _ _
  change Context Γ (both forwardFormula.encode
    (both reverseFormula.encode lexFormula.encode)) at hm
  have hf : Context Γ forwardFormula.encode := Context.conjunctionLeft hm
  have hf' : Context Γ (allCode 3 (point3 6).encode) := by
    rw [← forward_shape_old] at hf
    simpa [forwardAt, Formula.encode] using hf
  have hp := Context.mp hx (Context.mp hf' (.closed h3))
  have hw : Context Γ (existsCode 5 W.encode) := by
    have h := Context.mp hy (Context.mp hp (.closed h4))
    simpa [Formula.encode] using h
  simpa [selectedForwardBody, W] using Context.mp hw (.closed ha)

theorem reverse_coordinates_certificate : theoremCode (certificate reverse_coordinates) =
    imp productMatrix.encode (imp (member 2 32)
      (existsCode 30 (existsCode 31 selectedReverseBody.encode))) := certificate_correct _

theorem forward_output_certificate : theoremCode (certificate forward_output) =
    imp productMatrix.encode (imp (member 0 30) (imp (member 1 31)
      (existsCode 32 selectedForwardBody.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchPointWitness

#print axioms PASoundness.PAtoCompactProductMatchPointWitness.reverse_coordinates
#print axioms PASoundness.PAtoCompactProductMatchPointWitness.forward_output
#print axioms PASoundness.PAtoCompactProductMatchPointWitness.reverse_coordinates_certificate
#print axioms PASoundness.PAtoCompactProductMatchPointWitness.forward_output_certificate
