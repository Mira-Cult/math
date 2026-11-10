import PASoundness.PAtoCompactProductMatchPointWitness
import PASoundness.PAtoCompactScopedActiveReplace

/-! The target product's selected output for a pair of transported factor
coordinates. The product matrix, both coordinate memberships and the literal
uniqueness clause are retained. This does not yet collect a match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchTargetOutput

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactScopedActiveReplace

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseFrame : Formula := .imp productMatrix
  (.imp (.member 0 30) (.imp (.member 1 31) (.ex 35 (replace 32 35 selectedForwardBody))))

private def base_output : KDerivation baseFrame.encode := by
  have ha := (existentialAlpha 32 35 selectedForwardBody (by decide) (by decide) (by decide)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 31, member 0 30, productMatrix.encode]
  have hy : Context Γ (member 1 31) := .head _ _
  have hx : Context Γ (member 0 30) := .hypothesis (by simp [Γ])
  have hm : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 32 selectedForwardBody.encode) :=
    .mp hy (.mp hx (.mp hm (.closed forward_output)))
  simpa [baseFrame, Formula.encode] using Context.mp hw (.closed ha)

def targetMatrix : Formula :=
  replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 productMatrix)))
def targetTriple (a b c : Nat) : Formula := replace 6 45 (tripleFormula a b c)
def targetOutputBody : Formula := namedBoth (.member 44 35)
  (namedBoth (targetTriple 33 34 35)
    (.all 9 (.imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 35))))

def targetFrame : Formula :=
  replace 31 34 (replace 30 33
    (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 baseFrame)))))

theorem target_frame_shape : targetFrame =
    .imp targetMatrix (.imp (.member 42 33) (.imp (.member 43 34)
      (.ex 35 targetOutputBody))) := by decide

/-- Select an output for target coordinates 33,34, with output 35, retaining
membership, the actual triple and uniqueness for this coordinate pair. -/
def target_output : KDerivation
    (imp targetMatrix.encode (imp (member 42 33) (imp (member 43 34)
      (existsCode 35 targetOutputBody.encode)))) := by
  have h1 := replace_derivation 6 45 baseFrame (by decide) (by decide) base_output
  have h2 := replace_derivation 2 44 (replace 6 45 baseFrame) (by decide) (by decide) h1
  have h3 := replace_derivation 1 43 (replace 2 44 (replace 6 45 baseFrame))
    (by decide) (by decide) h2
  have h4 := replace_derivation 0 42 (replace 1 43 (replace 2 44 (replace 6 45 baseFrame)))
    (by decide) (by decide) h3
  have h5 := replace_derivation 30 33
    (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 baseFrame))))
    (by decide) (by decide) h4
  have h6 := replace_derivation 31 34
    (replace 30 33 (replace 0 42 (replace 1 43 (replace 2 44 (replace 6 45 baseFrame)))))
    (by decide) (by decide) h5
  change KDerivation targetFrame.encode at h6
  rw [target_frame_shape] at h6
  simpa [Formula.encode] using h6

theorem target_output_certificate : theoremCode (certificate target_output) =
    imp targetMatrix.encode (imp (member 42 33) (imp (member 43 34)
      (existsCode 35 targetOutputBody.encode))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchTargetOutput

#print axioms PASoundness.PAtoCompactProductMatchTargetOutput.target_output
#print axioms PASoundness.PAtoCompactProductMatchTargetOutput.target_output_certificate
