import Sude.FullReservationCancellationTransport
import Sude.PhysicalPairLineSum

/-! Same-stage physical midpoint and image-line preservation when a completion
fixes the full reservation containing all selected pair roles. No completion,
allocation, numerical bound, or later-flow existence is asserted. -/
namespace Sude
noncomputable section

/-- The selected endpoint entries, each original-stage mean, every selected
image-line sum and every same-stage centered pair score are unchanged.
The role inclusion and full-reservation pointwise fixedness are explicit. -/
theorem fixed_role_pair_line_transfer {n : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (a c : Cell n ≃ Fin (n*n)) (cells : (I × J) × Bool → Cell n)
    (roles full : Finset (Cell n)) (hcover : ∀ t, cells t ∈ roles)
    (hroles : roles ⊆ full) (hfixed : ∀ z ∈ full, entry c z = entry a z) :
    (∀ t, entry c (cells t) = entry a (cells t)) ∧
    (∀ j, fullReservationStageMean c cells j = fullReservationStageMean a cells j) ∧
    (∀ line : Finset (Cell n),
      (∑ z ∈ line ∩ Finset.univ.image cells, (entry c z : ℝ)) =
        ∑ z ∈ line ∩ Finset.univ.image cells, (entry a z : ℝ)) ∧
    (∀ w : I × J → ℝ,
      (∑ j, ∑ i, w (j,i) *
        ((((entry c (cells ((j,i),false)) : ℝ) + entry c (cells ((j,i),true))) / 2) -
          fullReservationStageMean c cells j)) =
      ∑ j, ∑ i, w (j,i) *
        ((((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2) -
          fullReservationStageMean a cells j)) := by
  classical
  have hpair : ∀ t, entry c (cells t) = entry a (cells t) := fun t => hfixed _ (hroles (hcover t))
  have hmean : ∀ j, fullReservationStageMean c cells j = fullReservationStageMean a cells j := by
    intro j
    simp only [fullReservationStageMean, hpair]
  refine ⟨hpair, hmean, ?_, ?_⟩
  · intro line
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hz).2
    rw [← ht, hpair]
  · intro w
    simp only [hpair, hmean]

end
end Sude
