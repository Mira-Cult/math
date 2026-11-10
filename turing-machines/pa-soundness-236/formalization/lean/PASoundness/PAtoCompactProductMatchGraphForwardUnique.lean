import PASoundness.PAtoCompactProductMatchReverseGraphCoverage

/-! Pointwise forward uniqueness of a supplied guarded product-match graph.
The endpoint guards and both graph edges are explicit antecedents. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchGraphForwardUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactProductMatchGraphOrder
open PASoundness.PAtoCompactProductMatchReverseGraphCoverage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def endpoints : Formula := namedBoth (.member 2 32) (namedBoth (.member 44 35)
  (namedBoth (.member 44 55) (namedBoth (graphFormula 58 32 35) (graphFormula 58 32 55))))

/-- Two guarded targets connected to one source are literally equal. -/
def forward_unique : KDerivation
    (imp actualMatch.encode (imp endpoints.encode (equal 55 35))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [endpoints.encode,actualMatch.encode]
  have he : Context Γ endpoints.encode := .head _ _
  have ha : Context Γ actualMatch.encode := .hypothesis (by simp [Γ])
  have he' : Context Γ (both (member 2 32) (both (member 44 35)
      (both (member 44 55) (both (graphFormula 58 32 35).encode (graphFormula 58 32 55).encode)))) := by
    simpa [endpoints, namedBoth, Formula.not, Formula.encode, both, neg] using he
  have hx := Context.conjunctionLeft he'
  have hy := Context.conjunctionLeft (Context.conjunctionRight he')
  have hz := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight he'))
  have hxy := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he')))
  have hxz := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight he')))
  have hfirst := Context.mp ha (.closed first_instance)
  have hfirst' : Context Γ (imp (both (member 2 32) (member 44 35))
      (both (imp (graphFormula 58 32 35).encode (both (member 2 32) path.encode))
        (imp (both (member 2 32) path.encode) (graphFormula 58 32 35).encode))) := by
    simpa [first_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hfirst
  have hp := Context.conjunctionRight (Context.mp hxy
    (Context.conjunctionLeft (Context.mp (Context.conjunctionIntro hx hy) hfirst')))
  have hsecond := Context.mp ha (.closed query_instance)
  have hsecond' : Context Γ (imp (both (member 2 32) (member 44 55))
      (both (imp (graphFormula 58 32 55).encode (both (member 2 32) (replace 35 55 path).encode))
        (imp (both (member 2 32) (replace 35 55 path).encode) (graphFormula 58 32 55).encode))) := by
    simpa [query_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hsecond
  have hq := Context.conjunctionRight (Context.mp hxz
    (Context.conjunctionLeft (Context.mp (Context.conjunctionIntro hx hz) hsecond')))
  simpa [Γ] using Context.mp hq (Context.mp hp (.closed path_functional))

theorem forward_unique_certificate : theoremCode (certificate forward_unique) =
    imp actualMatch.encode (imp endpoints.encode (equal 55 35)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchGraphForwardUnique

#print axioms PASoundness.PAtoCompactProductMatchGraphForwardUnique.forward_unique
#print axioms PASoundness.PAtoCompactProductMatchGraphForwardUnique.forward_unique_certificate
