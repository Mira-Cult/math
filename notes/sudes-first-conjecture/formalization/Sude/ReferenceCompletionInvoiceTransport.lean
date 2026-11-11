import Sude.FWPhysicalMidpointReference

/-! Transport a fresh reference across a completion that fixes its active
cells. The full line and every active correction receive the same adjustment.
This makes no claim about a later flow or existence of the completion. -/
namespace Sude
noncomputable section

/-- Complete the inactive cells simultaneously on an ordered square and its
reference, retaining the reference on the active cells. -/
theorem reference_completion_synchronise {α β : Type*} [DecidableEq α] [DecidableEq β]
    (a b c : α ≃ β) (active : Finset α)
    (hactive : ∀ x ∈ active, c x = a x)
    (hoff : ∀ x ∉ active, b x = a x)
    (himage : active.image b = active.image a) :
    ∃ d : α ≃ β,
      (∀ x ∈ active, d x = b x) ∧ (∀ x ∉ active, d x = c x) := by
  classical
  let d := b.trans (a.symm.trans c)
  refine ⟨d, ?_, ?_⟩
  · intro x hx
    have hm : b x ∈ active.image a := himage ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    have hy' : a.symm (b x) = y := by rw [← he, a.symm_apply_apply]
    change c (a.symm (b x)) = b x
    rw [hy', hactive y hy, he]
  · intro x hx
    change c (a.symm (b x)) = c x
    rw [hoff x hx, a.symm_apply_apply]

/-- Line differences, and hence any unchanged active correction, retain their
exact invoice after synchronized completion. -/
theorem reference_completion_invoice_transport {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (a b c d : α ≃ β) (active line : Finset α) (v : β → ℤ)
    (hnewActive : ∀ x ∈ active, c x = a x)
    (hrefActive : ∀ x ∈ active, d x = b x)
    (holdOff : ∀ x ∉ active, b x = a x)
    (hnewOff : ∀ x ∉ active, d x = c x) :
    (∑ x ∈ line, (v (d x) - v (c x))) =
      ∑ x ∈ line, (v (b x) - v (a x)) := by
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : x ∈ active
  · rw [hrefActive x h, hnewActive x h]
  · rw [hnewOff x h, holdOff x h]
    simp

/-- A doubled line invoice with any fixed active-network correction transfers
without increasing its error. The correction must already be known equal for
the two ordered squares; no network or flow existence is asserted here. -/
theorem reference_completion_doubled_invoice_transport {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (a b c d : α ≃ β) (active line : Finset α) (v : β → ℤ)
    (hnewActive : ∀ x ∈ active, c x = a x)
    (hrefActive : ∀ x ∈ active, d x = b x)
    (holdOff : ∀ x ∉ active, b x = a x)
    (hnewOff : ∀ x ∉ active, d x = c x) (correction : ℤ) :
    2 * (∑ x ∈ line, v (d x)) - (2 * (∑ x ∈ line, v (c x)) + correction) =
      2 * (∑ x ∈ line, v (b x)) - (2 * (∑ x ∈ line, v (a x)) + correction) := by
  have h := reference_completion_invoice_transport a b c d active line v
    hnewActive hrefActive holdOff hnewOff
  simp only [Finset.sum_sub_distrib] at h
  omega

end
end Sude
