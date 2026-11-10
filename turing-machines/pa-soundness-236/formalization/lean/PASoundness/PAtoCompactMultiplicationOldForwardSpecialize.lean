import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactZeroSuccessor

/-! Literal K specialization of the old product's forward clause to one
pair of members. It supplies the original output witness and its original
uniqueness condition, but does not extend the graph, discharge uniqueness
for a new graph, construct a product, or prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Product-style triple at fixed input labels 3 and 4. -/
def tripleAt (g out : Nat) : Formula := .ex 18
  (namedBoth (pairFormula 18 3 4) (graphFormula g 18 out))

/-- Original product output and uniqueness, with graph 10 and result 32. -/
def oldOutput : Formula := namedBoth (.member 32 5)
  (namedBoth (tripleAt 10 5)
    (.all 9 (.imp (namedBoth (.member 32 9) (tripleAt 10 9)) (.equal 9 5))))

def point4 : Formula := .imp (.member 31 4) (.ex 5 oldOutput)
def point3 : Formula := .imp (.member 30 3) (.all 4 point4)

/-- The old forward matrix with first input 30, second input 31, output 32,
and graph 10. All four names are syntactically distinct from its binders. -/
def oldForward : Formula := replace 6 10 (replace 2 32 (replace 1 31 (replace 0 30 forwardFormula)))

theorem old_forward_shape : oldForward = .all 3 point3 := by decide

/-- Applying the old forward clause to names 3 and 4 yields an output witness
with membership, the original triple edge and its original uniqueness clause. -/
def old_forward_at_point : KDerivation (imp oldForward.encode
    (imp (member 30 3) (imp (member 31 4) (existsCode 5 oldOutput.encode)))) := by
  have h3 := allSpecialize 3 point3 (by decide)
  have h3' : KDerivation (imp oldForward.encode (imp (member 30 3) (allCode 4 point4.encode))) := by
    simpa [old_forward_shape, point3, Formula.encode] using h3
  have h4 := allSpecialize 4 point4 (by decide)
  have h4' : KDerivation (imp (allCode 4 point4.encode)
      (imp (member 31 4) (existsCode 5 oldOutput.encode))) := by
    simpa [point4, Formula.encode] using h4
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 4, member 30 3, oldForward.encode]
  have hb : Context Γ (member 31 4) := .head _ _
  have ha : Context Γ (member 30 3) := .hypothesis (by simp [Γ])
  have hf : Context Γ oldForward.encode := .hypothesis (by simp [Γ])
  exact .mp hb (.mp (.mp ha (.mp hf (.closed h3'))) (.closed h4'))

theorem old_forward_at_point_certificate : theoremCode (certificate old_forward_at_point) =
    imp oldForward.encode (imp (member 30 3) (imp (member 31 4) (existsCode 5 oldOutput.encode))) :=
  certificate_correct old_forward_at_point
end PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardSpecialize.old_forward_shape
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardSpecialize.old_forward_at_point
#print axioms PASoundness.PAtoCompactMultiplicationOldForwardSpecialize.old_forward_at_point_certificate
