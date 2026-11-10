import PASoundness.PAtoCompactEquivNoShadow

/-! Finite syntax inventory and non-shadowing for the named successor
template. These properties do not by themselves prove any K equivalence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBaseInventory

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMapNoShadow
open PASoundness.PAtoCompactEquivNoShadow

/-- Exact finite syntax support of the successor template. -/
theorem successor_names : successorTemplate.names =
    ({0,1,2,3,4,5,6,7,8,19,20,21,22,30,31,32,33,34,35,36,37} : Finset Nat) := by
  decide

/-- Exact set of private bound labels, including repeated labels in
different disjoint branches only once. -/
theorem successor_binders : successorTemplate.binders =
    ({2,3,4,5,6,7,8,19,20,21,22,30,31,32,33,34,35,36,37} : Finset Nat) := by
  decide

/-- The template's only free source labels are the two inputs. -/
theorem successor_free : successorTemplate.free = ({0,1} : Finset Nat) := by
  decide

/-- No private binder shadows another occurrence of the same label in its
own scope. Reuse across separate branches is permitted. -/
theorem successor_binder_noShadow :
    ∀ x ∈ successorTemplate.binders, NoShadow x successorTemplate := by
  decide

theorem successor_allNoShadow (x : Nat) : NoShadow x successorTemplate := by
  by_cases hx : x ∈ successorTemplate.binders
  · exact successor_binder_noShadow x hx
  · exact noShadow_of_not_binder successorTemplate x hx

/-- The name mapping remains injective on private bound labels even if
the two operand labels coincide. No freshness condition on operands is
claimed here. -/
theorem succAt_allNoShadow (base x y z : Nat) : NoShadow z (succAt base x y) := by
  unfold succAt
  apply allNoShadow_map successorTemplate (twoMap base 0 1 x y) successor_allNoShadow
  intro a ha b hb he
  have ha0 : a ≠ 0 := fun h => templates_inputs_unbound.2.2.2.2.1 (h ▸ ha)
  have ha1 : a ≠ 1 := fun h => templates_inputs_unbound.2.2.2.2.2.1 (h ▸ ha)
  have hb0 : b ≠ 0 := fun h => templates_inputs_unbound.2.2.2.2.1 (h ▸ hb)
  have hb1 : b ≠ 1 := fun h => templates_inputs_unbound.2.2.2.2.2.1 (h ▸ hb)
  simp only [twoMap, ha0, ha1, hb0, hb1, if_false] at he
  omega

end PASoundness.PAtoCompactSuccBaseInventory

#print axioms PASoundness.PAtoCompactSuccBaseInventory.successor_names
#print axioms PASoundness.PAtoCompactSuccBaseInventory.successor_binders
#print axioms PASoundness.PAtoCompactSuccBaseInventory.successor_free
#print axioms PASoundness.PAtoCompactSuccBaseInventory.successor_binder_noShadow
#print axioms PASoundness.PAtoCompactSuccBaseInventory.successor_allNoShadow
#print axioms PASoundness.PAtoCompactSuccBaseInventory.succAt_allNoShadow
