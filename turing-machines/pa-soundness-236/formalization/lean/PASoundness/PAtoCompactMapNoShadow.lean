import PASoundness.PAtoCompactAlphaMapOne

/-! Injective renaming on bound labels preserves absence of nested shadowing.
No condition is imposed on free-name images, which may alias each other or
bound-label images. This is a syntactic support fact, not a K proof by itself. -/
namespace PASoundness.PAtoCompactMapNoShadow

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne

/-- If every original label is unshadowed and the renaming is injective on
the formula's bound labels, then every renamed label is unshadowed. -/
theorem allNoShadow_map (f : Formula) (g : Nat → Nat)
    (h : ∀ x, NoShadow x f)
    (hinj : ∀ a ∈ f.binders, ∀ b ∈ f.binders, g a = g b → a = b) :
    ∀ x, NoShadow x (mapNames g f) := by
  induction f with
  | truth | bottom | member | equal => intro x; trivial
  | imp a b ia ib =>
      intro x
      simp only [mapNames, NoShadow]
      constructor
      · apply ia
        · intro z; exact (h z).1
        · intro u hu v hv he
          apply hinj u _ v _ he <;> simp [Formula.binders, hu, hv]
      · apply ib
        · intro z; exact (h z).2
        · intro u hu v hv he
          apply hinj u _ v _ he <;> simp [Formula.binders, hu, hv]
  | all z a ih | ex z a ih =>
      intro x
      simp only [mapNames, NoShadow]
      constructor
      · intro hzx hx
        rw [mapNames_binders] at hx
        obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hx
        have hzv : z = v := by
          exact hinj z (by simp [Formula.binders]) v
            (by simp [Formula.binders, hv]) (hzx.trans he.symm)
        have hn : z ∉ a.binders := (h z).1 rfl
        exact hn (hzv ▸ hv)
      · apply ih
        · intro v; exact (h v).2
        · intro u hu v hv he
          apply hinj u _ v _ he <;> simp [Formula.binders, hu, hv]

end PASoundness.PAtoCompactMapNoShadow

#print axioms PASoundness.PAtoCompactMapNoShadow.allNoShadow_map
