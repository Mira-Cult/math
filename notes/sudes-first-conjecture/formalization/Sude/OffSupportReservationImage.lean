import Sude.ActualUnusedPool

/-! Value-image and unused-pool preservation for a cell permutation confined
to a subset of a supplied reservation.  This does not construct the
permutation, establish line bounds, or produce a CY completion. -/

namespace Sude
noncomputable section

/-- An off-reservation-fixed permutation maps the finite reservation to
itself. -/
theorem off_reservation_perm_image {α : Type*} [DecidableEq α]
    (full : Finset α) (σ : Equiv.Perm α)
    (hfix : ∀ x ∉ full, σ x = x) : full.image σ = full := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_contra hσx
    have hx' : σ x = x := σ.injective (hfix (σ x) hσx)
    rw [hx'] at hσx
    exact hσx hx
  · rw [Finset.card_image_of_injective _ σ.injective]

/-- Permuting cells within a reservation preserves its exact prescribed-value
image, the complement's value image, and the actual unused pool. The supplied
support may be any subset of the reservation, including the empty set. -/
theorem off_support_reservation_value_images {n : ℕ}
    (full support : Finset (Cell n)) (hsub : support ⊆ full)
    (σ : Equiv.Perm (Cell n)) (hfix : ∀ z ∉ support, σ z = z)
    (a : Cell n ≃ Fin (n*n)) :
    full.image (entry (σ.trans a)) = full.image (entry a) ∧
    (Finset.univ \ full).image (entry (σ.trans a)) =
      (Finset.univ \ full).image (entry a) ∧
    actualUnusedPool (σ.trans a) full = actualUnusedPool a full := by
  classical
  have hout : ∀ z ∉ full, σ z = z := fun z hz => hfix z (fun hs => hz (hsub hs))
  have himage : full.image σ = full := off_reservation_perm_image full σ hout
  have hfull : full.image (entry (σ.trans a)) = full.image (entry a) := by
    calc
      _ = (full.image σ).image (entry a) := by
        rw [Finset.image_image]
        rfl
      _ = _ := by rw [himage]
  have hcomp : (Finset.univ \ full).image (entry (σ.trans a)) =
      (Finset.univ \ full).image (entry a) := by
    apply Finset.image_congr
    intro z hz
    have hzfull : z ∉ full := (Finset.mem_sdiff.mp hz).2
    simp only [entry, Equiv.trans_apply, hout z hzfull]
  refine ⟨hfull, hcomp, ?_⟩
  unfold actualUnusedPool
  apply Finset.image_congr
  intro z hz
  have hzfull : z ∉ full := (Finset.mem_sdiff.mp hz).2
  apply Subtype.ext
  simp only [entryPool_val, entry, Equiv.trans_apply, hout z hzfull]

end
end Sude
