import PASoundness.PAtoCompactMapNoShadow

/-! The quotient-equivalence template has no nested binder shadowing, and
its concrete instance retains this property independently of operand aliasing.
This is a syntactic property, not by itself an alpha-equivalence proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivNoShadow

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactMapNoShadow

/-- A name absent from all binders cannot shadow itself. -/
theorem noShadow_of_not_binder (f : Formula) (x : Nat) (hx : x ∉ f.binders) :
    NoShadow x f := by
  induction f with
  | truth | bottom | member | equal => trivial
  | imp a b ia ib =>
      simp only [Formula.binders, Finset.mem_union, not_or] at hx
      exact ⟨ia hx.1, ib hx.2⟩
  | all z a ih | ex z a ih =>
      simp only [Formula.binders, Finset.mem_insert, not_or] at hx
      refine ⟨?_, ih hx.2⟩
      intro he
      exact False.elim (hx.1 he.symm)

def equivTemplate : Formula := normalizeBottom equivalentFormula

/-- A finite structural check covers every binder label of the template. -/
theorem template_binder_noShadow : ∀ x ∈ equivTemplate.binders, NoShadow x equivTemplate := by
  decide

theorem template_allNoShadow (x : Nat) : NoShadow x equivTemplate := by
  by_cases hx : x ∈ equivTemplate.binders
  · exact template_binder_noShadow x hx
  · exact noShadow_of_not_binder equivTemplate x hx

/-- Concrete operand names may coincide: only the private binder labels must
remain distinct under the template's name map. -/
theorem equivAt_allNoShadow (base x y : Nat) (z : Nat) : NoShadow z (equivAt base x y) := by
  unfold equivAt
  change NoShadow z (mapNames (twoMap base 0 1 x y) equivTemplate)
  apply allNoShadow_map equivTemplate (twoMap base 0 1 x y) template_allNoShadow
  intro a ha b hb he
  have ha0 : a ≠ 0 := fun h => templates_inputs_unbound.2.1 (h ▸ ha)
  have ha1 : a ≠ 1 := fun h => templates_inputs_unbound.2.2.1 (h ▸ ha)
  have hb0 : b ≠ 0 := fun h => templates_inputs_unbound.2.1 (h ▸ hb)
  have hb1 : b ≠ 1 := fun h => templates_inputs_unbound.2.2.1 (h ▸ hb)
  simp only [twoMap, ha0, ha1, hb0, hb1, if_false] at he
  omega

end PASoundness.PAtoCompactEquivNoShadow

#print axioms PASoundness.PAtoCompactEquivNoShadow.noShadow_of_not_binder
#print axioms PASoundness.PAtoCompactEquivNoShadow.template_binder_noShadow
#print axioms PASoundness.PAtoCompactEquivNoShadow.template_allNoShadow
#print axioms PASoundness.PAtoCompactEquivNoShadow.equivAt_allNoShadow
