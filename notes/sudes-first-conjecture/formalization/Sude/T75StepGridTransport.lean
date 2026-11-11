import Sude.StepGrid

/-! Support-only relabelling of an existing arbitrary-step subset-sum grid.
This does not construct a grid, prime pairs, or target values. -/
namespace Sude
noncomputable section

/-- An injective relabelling on the finite support preserves every covered
multiple of the same step, with the same radius and actual gap values. -/
theorem completeStepGrid_finite_relabel {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (gap : α → ℕ) (step radius : ℕ)
    (f : {x // x ∈ S} → β) (hf : Function.Injective f) (newGap : β → ℕ)
    (hgap : ∀ x, newGap (f x) = gap x.val)
    (hgrid : CompleteStepGrid S gap step radius) :
    CompleteStepGrid (S.attach.image f) newGap step radius := by
  intro t ht hstep
  obtain ⟨T, hT, hsum⟩ := hgrid t ht hstep
  let g : {x // x ∈ T} → β := fun x => f ⟨x.val, hT x.property⟩
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {x // x ∈ S} => z.val) (hf h)
  refine ⟨T.attach.image g, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨⟨x.val, hT x.property⟩, by simp, rfl⟩
  · rw [Finset.sum_image (fun x _ y _ h => hg h)]
    simpa [g, hgap, Finset.sum_attach] using hsum

end
end Sude
