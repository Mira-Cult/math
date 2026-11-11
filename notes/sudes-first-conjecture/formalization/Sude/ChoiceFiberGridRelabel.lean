import Sude.BridgePhysicalGrid

/-! Relabel two supplied abstract grids into the corresponding fibers of a
physical choice. The embeddings, gap alignment, and radii are all inputs. -/
namespace Sude
noncomputable section

/-- An injective map from each abstract support into the corresponding choice
fiber transports its complete even grid, retaining its own side radius. -/
theorem choice_fiber_complete_even_grids {α β : Type*} [DecidableEq α] [DecidableEq β]
    (support : Bool → Finset α) (abstractGap : Bool → α → ℕ)
    (radius : Bool → ℕ) (active : Finset β) (choice : β → Bool) (gap : β → ℕ)
    (label : (side : Bool) → {x // x ∈ support side} → β)
    (hinj : ∀ side, Function.Injective (label side))
    (halign : ∀ side x, label side x ∈ active ∧ choice (label side x) = side ∧
      gap (label side x) = abstractGap side x.val)
    (hgrid : ∀ side, CompleteEvenGrid (support side) (abstractGap side) (radius side)) :
    ∀ side, CompleteEvenGrid (active.filter fun i => choice i = side) gap (radius side) := by
  classical
  intro side
  have h := completeEvenGrid_finite_relabel (support side) (abstractGap side) (radius side)
    (label side) (hinj side) gap (fun x => (halign side x).2.2) (hgrid side)
  have hsub : (support side).attach.image (label side) ⊆ active.filter (fun i => choice i = side) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨(halign side x).1, (halign side x).2.1⟩
  intro t ht heven
  obtain ⟨T, hT, hsum⟩ := h t ht heven
  exact ⟨T, hT.trans hsub, hsum⟩

end
end Sude
