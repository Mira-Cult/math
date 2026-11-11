import Sude.CentralExactPool
import Sude.APInterval
namespace Sude
noncomputable section

/-- Exact separate charging of old and newly reserved values in any interval. -/
theorem reserved_value_deletion_exact {n : ℕ} (a b : Cell n ≃ Fin (n*n))
    (R D : Finset (Cell n)) (I : Finset ℕ)
    (hdis : Disjoint R D) (hfixed : ∀ z ∈ R, entry b z = entry a z) :
    (I ∩ (R ∪ D).image (entry b)).card =
      (I ∩ R.image (entry a)).card + (I ∩ D.image (entry b)).card := by
  classical
  have hR : R.image (entry b) = R.image (entry a) :=
    Finset.image_congr (fun z hz => hfixed z hz)
  have hdisImage : Disjoint (R.image (entry b)) (D.image (entry b)) := by
    apply Finset.disjoint_left.mpr
    intro p hpR hpD
    obtain ⟨r, hr, hrp⟩ := Finset.mem_image.mp hpR
    obtain ⟨d, hd, hdp⟩ := Finset.mem_image.mp hpD
    have heq : r = d := (entry_injective b) (hrp.trans hdp.symm)
    exact (Finset.disjoint_left.mp hdis) hr (heq ▸ hd)
  have hdisI : Disjoint (I ∩ R.image (entry b)) (I ∩ D.image (entry b)) := by
    apply Finset.disjoint_left.mpr
    intro p hpR hpD
    exact (Finset.disjoint_left.mp hdisImage) (Finset.mem_inter.mp hpR).2 (Finset.mem_inter.mp hpD).2
  rw [Finset.image_union, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisI, hR]

theorem reserved_value_deletion_bound {n : ℕ} (a b : Cell n ≃ Fin (n*n))
    (R D : Finset (Cell n)) (I : Finset ℕ)
    (hdis : Disjoint R D) (hfixed : ∀ z ∈ R, entry b z = entry a z) :
    (I ∩ (R ∪ D).image (entry b)).card ≤ (I ∩ R.image (entry a)).card + D.card := by
  rw [reserved_value_deletion_exact a b R D I hdis hfixed]
  have h := Finset.card_le_card (Finset.inter_subset_right : I ∩ D.image (entry b) ⊆ D.image (entry b))
  rw [Finset.card_image_of_injective _ (entry_injective b)] at h
  omega

theorem post_diagonal_interval_deletion_bound {n : ℕ} (a b : Cell n ≃ Fin (n*n))
    (R : Finset (Cell n)) (lo hi : ℝ)
    (hfixed : ∀ z ∈ R, entry b z = entry a z) :
    (apInterval lo hi 2 1 ∩ (R ∪ unreservedDiagonalCells R).image (entry b)).card ≤
      (apInterval lo hi 2 1 ∩ R.image (entry a)).card + (unreservedDiagonalCells R).card := by
  apply reserved_value_deletion_bound a b R (unreservedDiagonalCells R) _ ?_ hfixed
  apply Finset.disjoint_left.mpr
  intro z hz hd
  exact (Finset.mem_sdiff.mp hd).2 hz
theorem unreserved_diagonal_card_le_two_n_sub_one {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (reserved : Finset (Cell n)) :
    (unreservedDiagonalCells reserved).card ≤ 2 * n - 1 := by
  classical
  have hs : unreservedDiagonalCells reserved ⊆ mainCells n ∪ antiCells n := Finset.sdiff_subset
  have hu := Finset.card_union_add_card_inter (mainCells n) (antiCells n)
  rw [main_anti_intersection hn hodd, mainCells_card, antiCells_card] at hu
  simp only [Finset.card_singleton] at hu
  have hc := Finset.card_le_card hs
  omega

/-- A post-diagonal interval charges the old reservation at the same exact
endpoints, plus at most 2n−1 newly reserved values. This does not compare
those endpoints with a pre-diagonal interval or prove a numerical gate. -/
theorem post_diagonal_interval_deletion_two_n {n : ℕ} (a b : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (lo hi : ℝ) (hn : 0 < n) (hodd : Odd n)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z) :
    (apInterval lo hi 2 1 ∩ (reserved ∪ unreservedDiagonalCells reserved).image (entry b)).card ≤
      (apInterval lo hi 2 1 ∩ reserved.image (entry a)).card + (2 * n - 1) := by
  have h := post_diagonal_interval_deletion_bound a b reserved lo hi hfixed
  have hd := unreserved_diagonal_card_le_two_n_sub_one hn hodd reserved
  omega

end
end Sude
