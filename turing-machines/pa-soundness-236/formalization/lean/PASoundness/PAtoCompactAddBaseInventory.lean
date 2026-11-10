import PASoundness.PAtoCompactEquivNoShadow

/-! Exact syntax support and non-shadowing for the normalized named
addition template. These facts do not prove K equivalence across bases. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAddBaseInventory

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactMapNoShadow PASoundness.PAtoCompactEquivNoShadow

def addTemplate : Formula := normalizeBottom additionFormula

theorem addition_names : addTemplate.names =
    ({2,3,4,5,6,19,20,21,22,30,31,32,33,34,35} : Finset Nat) := by decide

theorem addition_binders : addTemplate.binders =
    ({2,3,4,5,6,19,20,21,22,33,34,35} : Finset Nat) := by decide

theorem addition_free : addTemplate.free = ({30,31,32} : Finset Nat) := by decide

/-- Reuse of private names in disjoint branches does not shadow a name in
its own scope. -/
theorem addition_binder_noShadow : ∀ x ∈ addTemplate.binders, NoShadow x addTemplate := by
  decide

theorem addition_allNoShadow (x : Nat) : NoShadow x addTemplate := by
  by_cases hx : x ∈ addTemplate.binders
  · exact addition_binder_noShadow x hx
  · exact noShadow_of_not_binder addTemplate x hx

/-- The map is injective on private binder labels even if any of the
three operand labels coincide. No operand freshness is assumed here. -/
theorem addAt_allNoShadow (base x y z w : Nat) : NoShadow w (addAt base x y z) := by
  unfold addAt
  change NoShadow w (mapNames (threeMap base 30 31 32 x y z) addTemplate)
  apply allNoShadow_map addTemplate (threeMap base 30 31 32 x y z) addition_allNoShadow
  intro a ha b hb he
  have ha30 : a ≠ 30 := by intro h; subst a; simp [addition_binders] at ha
  have ha31 : a ≠ 31 := by intro h; subst a; simp [addition_binders] at ha
  have ha32 : a ≠ 32 := by intro h; subst a; simp [addition_binders] at ha
  have hb30 : b ≠ 30 := by intro h; subst b; simp [addition_binders] at hb
  have hb31 : b ≠ 31 := by intro h; subst b; simp [addition_binders] at hb
  have hb32 : b ≠ 32 := by intro h; subst b; simp [addition_binders] at hb
  simp only [threeMap, ha30, ha31, ha32, hb30, hb31, hb32, if_false] at he
  omega

end PASoundness.PAtoCompactAddBaseInventory

#print axioms PASoundness.PAtoCompactAddBaseInventory.addition_names
#print axioms PASoundness.PAtoCompactAddBaseInventory.addition_binders
#print axioms PASoundness.PAtoCompactAddBaseInventory.addition_free
#print axioms PASoundness.PAtoCompactAddBaseInventory.addition_binder_noShadow
#print axioms PASoundness.PAtoCompactAddBaseInventory.addition_allNoShadow
#print axioms PASoundness.PAtoCompactAddBaseInventory.addAt_allNoShadow
