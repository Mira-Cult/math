import PASoundness.PAtoCompactProductOutputInsideSelected
import PASoundness.PAtoCompactProductOutputTripleExtension

/-! Combine an inside-source selected point and a triple adjunction using the
same coordinate and image-output witnesses. The partial invariant of the new
graph is not established by this pointwise extension. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputInsideExtension

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactProductOutputCollectionInsideConditional
open PASoundness.PAtoCompactProductOutputInsideSelected PASoundness.PAtoCompactProductOutputTripleExtension

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def selectedWithExtension : Formula := namedBoth relocatedBody newStatement

/-- The graph extension uses the SAME factor labels 30,31 and image output 33
selected for source endpoint 74, and starts from the free old graph 58. -/
def inside_selected_extension : KDerivation (imp assumptions.encode (imp (member 0 74)
    (existsCode 30 (existsCode 31 (existsCode 33 selectedWithExtension.encode))))) := by
  have hpoint : KDerivation (imp relocatedBody.encode selectedWithExtension.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [relocatedBody.encode]
    have hp : Context Γ relocatedBody.encode := .head _ _
    have he : Context Γ newStatement.encode := .closed selected_triple_extension
    simpa [selectedWithExtension, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using Context.conjunctionIntro hp he
  have h33 := existsCongr 33 hpoint
  have h31 := existsCongr 31 h33
  have h30 := existsCongr 30 h31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 74, assumptions.encode]
  have hx : Context Γ (member 0 74) := .head _ _
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hp := Context.mp hx (Context.mp hh (.closed inside_selected_point))
  exact .mp hp (.closed h30)

theorem inside_selected_extension_certificate : theoremCode (certificate inside_selected_extension) =
    imp assumptions.encode (imp (member 0 74)
      (existsCode 30 (existsCode 31 (existsCode 33 selectedWithExtension.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductOutputInsideExtension

#print axioms PASoundness.PAtoCompactProductOutputInsideExtension.inside_selected_extension
#print axioms PASoundness.PAtoCompactProductOutputInsideExtension.inside_selected_extension_certificate
