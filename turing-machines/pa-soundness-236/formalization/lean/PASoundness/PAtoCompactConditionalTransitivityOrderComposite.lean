import PASoundness.PAtoCompactConditionalTransitivityOrderPaths
import PASoundness.PAtoCompactConditionalTransitivityElimSecond
import PASoundness.CompactFreshen

/-! Guarded pointwise order transfer through two composite edges.
The composition graph and the two source order clauses are explicitly
supplied. No graph construction, quantified order clause, or quotient
transitivity is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactConditionalTransitivityOrderComposite
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactConditionalTransitivityPoint
open PASoundness.PAtoCompactConditionalTransitivityElimSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderSecond
open PASoundness.PAtoCompactConditionalTransitivityOrderGuard
open PASoundness.PAtoCompactConditionalTransitivityOrderPaths
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Both actual order clauses, restricted composition, endpoint domains,
and the two composite edges. No unguarded graph edge is assumed. -/
def premises : Formula := namedBoth orderFormula (namedBoth secondOrder
  (namedBoth composition (namedBoth (.member 0 2) (namedBoth (.member 0 4)
    (namedBoth (.member 8 3) (namedBoth (.member 8 5)
      (namedBoth edge secondEdge)))))))

def conclusion : Formula := namedBoth (.imp (.member 4 2) (.member 5 3))
  (.imp (.member 5 3) (.member 4 2))

private theorem premises_names_lt : ∀ v ∈ premises.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ premises.names.sup id at hm
  have hb : premises.names.sup id < 30 := by decide
  omega

/-- Both intermediate names are vacuous for the premise only after a
checked alpha-freshening of its internally bound names. -/
private def freshPremises := freshen premises 30 premises_names_lt
private theorem fresh_no10 : 10 ∉ freshPremises.formula.names := by decide
private theorem fresh_no11 : 11 ∉ freshPremises.formula.names := by decide
private def premisesVacuity (v : Nat) (h : v ∉ freshPremises.formula.names) :
    KDerivation (imp premises.encode (allCode v premises.encode)) :=
  compose freshPremises.equivalent.forward
    (compose (freshPremises.formula.vacuity v h)
      (allCongr v freshPremises.equivalent.backward))

/-- Given restricted composition, both source order clauses, the four
endpoint memberships and two composite edges, K derives the target order
equivalence. Both intermediate witnesses are existentially eliminated. -/
def guarded_composite_order : KDerivation (imp premises.encode conclusion.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [premises.encode]
  have h : Context Γ premises.encode := Context.head [] _
  have ho : Context Γ orderFormula.encode := Context.conjunctionLeft h
  have htail := Context.conjunctionRight h
  have hs : Context Γ secondOrder.encode := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hc : Context Γ composition.encode := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have ha : Context Γ (member 0 2) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have ha' : Context Γ (member 0 4) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hb : Context Γ (member 8 3) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have hb' : Context Γ (member 8 5) := Context.conjunctionLeft htail
  have htail := Context.conjunctionRight htail
  have he : Context Γ edge.encode := Context.conjunctionLeft htail
  have he' : Context Γ secondEdge.encode := Context.conjunctionRight htail
  have hpath10 : Context Γ (existsCode 10 pathBody.encode) := by
    simpa only [path, Formula.encode] using
      (.mp he (.mp hb (.mp ha (.mp hc (.closed edge_to_path)))))
  have hpath11 : Context Γ (existsCode 11 secondBody11.encode) := by
    simpa only [secondPath, Formula.encode] using
      (.mp he' (.mp hb' (.mp ha' (.mp hc (.closed second_edge_to_path)))))
  have hlocal : Context (secondBody11.encode :: pathBody.encode :: Γ) conclusion.encode := by
    let Δ := secondBody11.encode :: pathBody.encode :: Γ
    have ho' : Context Δ orderFormula.encode := .under (.under ho _) _
    have hs' : Context Δ secondOrder.encode := .under (.under hs _) _
    have ha1 : Context Δ (member 0 2) := .under (.under ha _) _
    have ha2 : Context Δ (member 0 4) := .under (.under ha' _) _
    have hb1 : Context Δ (member 8 3) := .under (.under hb _) _
    have hb2 : Context Δ (member 8 5) := .under (.under hb' _) _
    have hp10 : Context Δ path10 := by
      change Context Δ pathBody.encode
      exact Context.under (Context.head Γ pathBody.encode) secondBody11.encode
    have hp11 : Context Δ path11 := by
      change Context Δ secondBody11.encode
      exact Context.head (pathBody.encode :: Γ) secondBody11.encode
    have hg : Context Δ pathGuards := Context.conjunctionIntro ha1
      (Context.conjunctionIntro ha2 (Context.conjunctionIntro hb1
        (Context.conjunctionIntro hb2 (Context.conjunctionIntro hp10 hp11))))
    simpa [conclusion, namedBoth, Formula.encode, sameOrder, both, neg] using
      (Context.mp hg (Context.mp hs' (Context.mp ho' (.closed order_from_paths))))
  have hv11 : ∀ h, h ∈ pathBody.encode :: Γ → KDerivation (imp h (allCode 11 h)) := by
    intro f hf
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hf
    by_cases heq : f = pathBody.encode
    · subst f
      exact pathBody.vacuity 11 (by decide)
    · have heq' : f = premises.encode := hf.resolve_left heq
      subst f
      exact premisesVacuity 11 fresh_no11
  have h11 : Context (pathBody.encode :: Γ) conclusion.encode :=
    Context.existsElim (conclusion.vacuity 11 (by decide))
      (Context.generalize 11 hv11 (Context.deduction hlocal))
      (Context.under hpath11 pathBody.encode)
  have hv10 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 10 h)) := by
    intro f hf
    have heq : f = premises.encode := by simpa [Γ] using hf
    subst f
    exact premisesVacuity 10 fresh_no10
  exact Context.existsElim (conclusion.vacuity 10 (by decide))
    (Context.generalize 10 hv10 (Context.deduction h11)) hpath10

theorem guarded_composite_order_certificate :
    theoremCode (certificate guarded_composite_order) = imp premises.encode conclusion.encode :=
  certificate_correct guarded_composite_order

end PASoundness.PAtoCompactConditionalTransitivityOrderComposite

#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderComposite.guarded_composite_order
#print axioms PASoundness.PAtoCompactConditionalTransitivityOrderComposite.guarded_composite_order_certificate
