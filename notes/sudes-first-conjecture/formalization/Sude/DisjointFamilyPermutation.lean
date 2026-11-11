import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-! Simultaneously map disjoint labelled populations to disjoint slots by
one permutation. The ambient complement goes to the ambient complement. -/
namespace Sude
noncomputable section

/-- Equal-cardinality finite disjoint families admit a single permutation
mapping each source family exactly onto its corresponding target family.
The map may move labels outside the families, but maps their complement to
the complement of the target union. -/
theorem disjoint_family_permutation {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq α] (S T : ι → Finset α)
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hT : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hcard : ∀ i, (S i).card = (T i).card) :
    ∃ σ : Equiv.Perm α,
      (∀ i, (S i).image σ = T i) ∧
      ∀ x, (∀ i, x ∉ S i) ↔ (∀ i, σ x ∉ T i) := by
  classical
  let e : ∀ i, ↥(S i) ≃ ↥(T i) := fun i => Finset.equivOfCardEq (hcard i)
  let f : (Σ i, ↥(S i)) → α := fun a => a.2.1
  let g : (Σ i, ↥(S i)) → α := fun a => (e a.1 a.2).1
  have hf : Function.Injective f := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change a.1 = b.1 at h
    have hij : i = j := by
      by_contra hij
      have ha : a.1 ∈ S i := a.2
      have hb : a.1 ∈ S j := by rw [h]; exact b.2
      exact (Finset.disjoint_left.mp (hS i j hij)) ha hb
    subst j
    have hab : a = b := Subtype.ext h
    subst b
    rfl
  have hg : Function.Injective g := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    change (e i a).1 = (e j b).1 at h
    have hij : i = j := by
      by_contra hij
      have ha : (e i a).1 ∈ T i := (e i a).2
      have hb : (e i a).1 ∈ T j := by rw [h]; exact (e j b).2
      exact (Finset.disjoint_left.mp (hT i j hij)) ha hb
    subst j
    have hab : a = b := (e i).injective (Subtype.ext h)
    subst b
    rfl
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have himage : ∀ i, (S i).image σ = T i := by
    intro i
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hh := hσ ⟨i, ⟨x, hx⟩⟩
      have hm : (e i ⟨x, hx⟩).1 ∈ T i := (e i ⟨x, hx⟩).2
      simpa [f, g] using hh ▸ hm
    · rw [Finset.card_image_of_injective _ σ.injective, hcard]
  refine ⟨σ, himage, ?_⟩
  intro x
  constructor
  · intro hx i hxi
    have hm : σ x ∈ (S i).image σ := by rw [himage]; exact hxi
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hm
    exact hx i ((σ.injective heq) ▸ hy)
  · intro hx i hxi
    apply hx i
    rw [← himage]
    exact Finset.mem_image.mpr ⟨x, hxi, rfl⟩

end
end Sude
