import PASoundness.PAtoCompactTermTranslation

/-! Extensionality of raw named-syntax renaming. These are syntactic
identities, not K proofs of equivalence between renamed formulas. -/
namespace PASoundness.PAtoCompactMapNamesCongr

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation

/-- Full named renaming depends only on names occurring in the syntax,
including binders. No injectivity or freshness condition is required. -/
theorem mapNames_congr (a : Formula) (f g : Nat → Nat)
    (h : ∀ x ∈ a.names, f x = g x) : mapNames f a = mapNames g a := by
  induction a with
  | truth | bottom => rfl
  | member x y | equal x y =>
      have hx : f x = g x := h x (by simp [Formula.names])
      have hy : f y = g y := h y (by simp [Formula.names])
      simp [mapNames, hx, hy]
  | imp a b ia ib =>
      have ha : ∀ x ∈ a.names, f x = g x := by
        intro x hx
        exact h x (by simp [Formula.names, hx])
      have hb : ∀ x ∈ b.names, f x = g x := by
        intro x hx
        exact h x (by simp [Formula.names, hx])
      simp [mapNames, ia ha, ib hb]
  | all x a ih | ex x a ih =>
      have hx : f x = g x := h x (by simp [Formula.names])
      have ha : ∀ y ∈ a.names, f y = g y := by
        intro y hy
        exact h y (by simp [Formula.names, hy])
      simp [mapNames, hx, ih ha]

/-- A renaming fixing every occurring name preserves the named formula. -/
theorem mapNames_id (a : Formula) : mapNames id a = a := by
  induction a with
  | truth | bottom | member | equal => rfl
  | imp a b ia ib => simp [mapNames, ia, ib]
  | all x a ih | ex x a ih => simp [mapNames, ih]

theorem mapNames_id_on_names (a : Formula) (f : Nat → Nat)
    (h : ∀ x ∈ a.names, f x = x) : mapNames f a = a :=
  (mapNames_congr a f id h).trans (mapNames_id a)

/-- Named conjunction commutes literally with name mapping. -/
theorem mapNames_andF (f : Nat → Nat) (a b : Formula) :
    mapNames f (andF a b) = andF (mapNames f a) (mapNames f b) := by
  rfl

end PASoundness.PAtoCompactMapNamesCongr

#print axioms PASoundness.PAtoCompactMapNamesCongr.mapNames_congr
#print axioms PASoundness.PAtoCompactMapNamesCongr.mapNames_id
#print axioms PASoundness.PAtoCompactMapNamesCongr.mapNames_id_on_names
#print axioms PASoundness.PAtoCompactMapNamesCongr.mapNames_andF
