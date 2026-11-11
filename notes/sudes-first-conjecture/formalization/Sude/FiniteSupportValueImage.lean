import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Function

/-! Equal full value ranges and agreement off a finite support force the
same support values. This statement is independent of any square or network. -/
namespace Sude

/-- Injective maps with equal full ranges that agree outside a finite set
have the same image of that set. The domain need not itself be finite. -/
theorem finite_support_value_image_eq {α β : Type*} [DecidableEq β]
    (A : Finset α) (f g : α → β)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrange : Set.range f = Set.range g)
    (houtside : ∀ x, x ∉ A → f x = g x) :
    A.image f = A.image g := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hmem : f x ∈ Set.range g := hrange ▸ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    refine Finset.mem_image.mpr ⟨z, ?_, hz⟩
    by_contra hza
    have heq : f z = f x := (houtside z hza).trans hz
    have hzx : z = x := hf heq
    exact hza (hzx.symm ▸ hx)
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hmem : g x ∈ Set.range f := hrange.symm ▸ ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    refine Finset.mem_image.mpr ⟨z, ?_, hz⟩
    by_contra hza
    have heq : g z = g x := (houtside z hza).symm.trans hz
    have hzx : z = x := hg heq
    exact hza (hzx.symm ▸ hx)

end Sude
