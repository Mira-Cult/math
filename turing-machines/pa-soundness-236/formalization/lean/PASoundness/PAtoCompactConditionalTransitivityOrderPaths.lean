import PASoundness.PAtoCompactConditionalTransitivityOrderInstance

/-! Literal pointwise order transfer given two explicit composition paths.
The two path witnesses, the four endpoint memberships, and both source order
clauses remain explicit premises. No graph is constructed and no unguarded
edge outside a domain is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderPaths
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityOrderSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderGuard
open PASoundness.PAtoCompactConditionalTransitivityOrderInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- First supplied path, whose middle point is name 10. -/
def path10 : Nat := both (member 1 10)
  (both (graphFormula 6 2 10).encode (graphFormula 7 10 3).encode)

/-- Second supplied path, whose middle point is name 11. -/
def path11 : Nat := both (member 1 11)
  (both (graphFormula 6 4 11).encode (graphFormula 7 11 5).encode)

/-- The source and target membership guards, with the two supplied paths. -/
def pathGuards : Nat := both (member 0 2) (both (member 0 4)
  (both (member 8 3) (both (member 8 5) (both path10 path11))))

/-- K derives target order agreement from the two literal order clauses,
the endpoint guards and the displayed paths with their original witnesses. -/
def order_from_paths : KDerivation
    (imp orderFormula.encode (imp secondOrder.encode
      (imp pathGuards (sameOrder (member 4 2) (member 5 3))))) := by
  let Γ := [pathGuards, secondOrder.encode, orderFormula.encode]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ho : Context Γ orderFormula.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ secondOrder.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ pathGuards := Context.head _ _
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft hg
  have ha' : Context Γ (member 0 4) := Context.conjunctionLeft (Context.conjunctionRight hg)
  have hc : Context Γ (member 8 3) := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg))
  have hc' : Context Γ (member 8 5) := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg)))
  have hpaths : Context Γ (both path10 path11) := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg)))
  have hp : Context Γ path10 := Context.conjunctionLeft hpaths
  have hq : Context Γ path11 := Context.conjunctionRight hpaths
  have hb : Context Γ (member 1 10) := Context.conjunctionLeft hp
  have hb' : Context Γ (member 1 11) := Context.conjunctionLeft hq
  have hf : Context Γ (graphFormula 6 2 10).encode := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hf' : Context Γ (graphFormula 6 4 11).encode := Context.conjunctionLeft (Context.conjunctionRight hq)
  have hgg : Context Γ (graphFormula 7 10 3).encode := Context.conjunctionRight (Context.conjunctionRight hp)
  have hgg' : Context Γ (graphFormula 7 11 5).encode := Context.conjunctionRight (Context.conjunctionRight hq)
  have hfirst : Context Γ firstGuard :=
    Context.conjunctionIntro ha (Context.conjunctionIntro ha' (Context.conjunctionIntro hb
      (Context.conjunctionIntro hb' (Context.conjunctionIntro hf hf'))))
  have hsecond : Context Γ secondGuard :=
    Context.conjunctionIntro hb (Context.conjunctionIntro hb' (Context.conjunctionIntro hc
      (Context.conjunctionIntro hc' (Context.conjunctionIntro hgg hgg'))))
  exact .mp (Context.conjunctionIntro hfirst hsecond)
    (.mp hs (.mp ho (.closed guarded_order_from_clauses)))

theorem order_from_paths_certificate :
    theoremCode (certificate order_from_paths) =
      imp orderFormula.encode (imp secondOrder.encode
        (imp pathGuards (sameOrder (member 4 2) (member 5 3)))) :=
  certificate_correct order_from_paths

end PASoundness.PAtoCompactConditionalTransitivityOrderPaths

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderPaths.order_from_paths
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderPaths.order_from_paths_certificate
