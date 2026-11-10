import PASoundness.PAtoCompactEquivNoShadow

/-! Finite named-syntax inventory and non-shadowing for the multiplication
template. These results do not by themselves prove any K equivalence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMulBaseInventory

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMapNoShadow
open PASoundness.PAtoCompactEquivNoShadow

/-- Exact finite syntax support of the normalized multiplication template. -/
theorem product_names : (normalizeBottom productFormula).names =
    ({0,1,2,3,4,5,6,7,8,9,18,19,20,21,22} : Finset Nat) := by
  decide

/-- Exact set of private bound labels. Repeated labels in separate branches
occur only once in the set. -/
theorem product_binders : (normalizeBottom productFormula).binders =
    ({3,4,5,6,7,8,9,18,19,20,21,22} : Finset Nat) := by
  decide

/-- The only free source labels are the three input placeholders. -/
theorem product_free : (normalizeBottom productFormula).free = ({0,1,2} : Finset Nat) := by
  decide

/-- No binder shadows the same label in its own scope. Reuse in disjoint
branches is permitted. -/
theorem product_binder_noShadow :
    ∀ x ∈ (normalizeBottom productFormula).binders,
      NoShadow x (normalizeBottom productFormula) := by
  decide

theorem product_allNoShadow (x : Nat) : NoShadow x (normalizeBottom productFormula) := by
  by_cases hx : x ∈ (normalizeBottom productFormula).binders
  · exact product_binder_noShadow x hx
  · exact noShadow_of_not_binder (normalizeBottom productFormula) x hx

/-- Mapping the private binders stays injective even when any of the three
operand labels coincide. This is not an operand freshness claim. -/
theorem mulAt_allNoShadow (base x y z w : Nat) : NoShadow w (mulAt base x y z) := by
  unfold mulAt
  apply allNoShadow_map (normalizeBottom productFormula) (threeMap base 0 1 2 x y z)
    product_allNoShadow
  intro a ha b hb he
  have hin : 0 ∉ (normalizeBottom productFormula).binders ∧
      1 ∉ (normalizeBottom productFormula).binders ∧
      2 ∉ (normalizeBottom productFormula).binders := by decide
  have ha0 : a ≠ 0 := fun h => hin.1 (h ▸ ha)
  have ha1 : a ≠ 1 := fun h => hin.2.1 (h ▸ ha)
  have ha2 : a ≠ 2 := fun h => hin.2.2 (h ▸ ha)
  have hb0 : b ≠ 0 := fun h => hin.1 (h ▸ hb)
  have hb1 : b ≠ 1 := fun h => hin.2.1 (h ▸ hb)
  have hb2 : b ≠ 2 := fun h => hin.2.2 (h ▸ hb)
  simp only [threeMap, ha0, ha1, ha2, hb0, hb1, hb2, if_false] at he
  omega

end PASoundness.PAtoCompactMulBaseInventory

#print axioms PASoundness.PAtoCompactMulBaseInventory.product_names
#print axioms PASoundness.PAtoCompactMulBaseInventory.product_binders
#print axioms PASoundness.PAtoCompactMulBaseInventory.product_free
#print axioms PASoundness.PAtoCompactMulBaseInventory.product_binder_noShadow
#print axioms PASoundness.PAtoCompactMulBaseInventory.product_allNoShadow
#print axioms PASoundness.PAtoCompactMulBaseInventory.mulAt_allNoShadow
