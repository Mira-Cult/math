import Sude.CentralOddDiagonal
import Sude.ActualUnusedPool

/-! Central diagonal placement from the exact unused prescribed pool. -/
namespace Sude
noncomputable section

def unreservedDiagonalCells {n : ℕ} (reserved : Finset (Cell n)) : Finset (Cell n) :=
  (mainCells n ∪ antiCells n) \ reserved

/-- The actual diagonal-cell partition covers exactly the two diagonals'
previously unreserved cells, with the shared center counted once. -/
theorem unreservedDiagonalCells_partition {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (reserved : Finset (Cell n)) (hcenter : centralCell n hn ∉ reserved) :
    ({centralCell n hn} : Finset (Cell n)) ∪ centralFreeMain hn reserved ∪
        centralFreeAnti hn reserved = unreservedDiagonalCells reserved := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hmain, hanti⟩ :=
    central_free_diagonal_geometry hn hodd reserved hcenter
  unfold unreservedDiagonalCells
  rw [Finset.union_sdiff_distrib, ← hmain, ← hanti]
  ext z
  simp only [Finset.mem_union]
  tauto

/-- The CC2--CC3 diagonal construction with the stock defined as exactly the
unreserved values of the original prescribed pool. The newly unused pool is
proved equal to that actual stock with the three selected batches removed.
Stock distribution and mean bounds are still explicit inputs. -/
theorem central_place_odd_diagonals_exact_pool {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (c η : ℝ) (hη : 0 < η) (hn : 20 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserved : 4 * reserved.card ≤ n * n)
    (hmean : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - c| ≤ η / 4)
    (hlow : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      ((actualUnusedPool a reserved).filter
        (fun v => c - η < centralPoolValue v ∧ centralPoolValue v ≤ c - η / 2)).card)
    (hhigh : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      ((actualUnusedPool a reserved).filter
        (fun v => c + η / 2 < centralPoolValue v ∧ centralPoolValue v ≤ c + η)).card) :
    ∃ (b : Cell n ≃ Fin (n * n)) (A B C : Finset (pool n)),
      A ⊆ actualUnusedPool a reserved ∧
      B ⊆ actualUnusedPool a reserved \ A ∧ C ⊆ (actualUnusedPool a reserved \ A) \ B ∧
      A.card = 1 ∧ B.card = (centralFreeMain (by omega) reserved).card ∧
      C.card = (centralFreeAnti (by omega) reserved).card ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ z ∈ unreservedDiagonalCells reserved, |(entry b z : ℝ) - c| ≤ η) ∧
      actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved) =
        ((actualUnusedPool a reserved \ A) \ B) \ C ∧
      n * n / 2 ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |(∑ z ∈ unreservedDiagonalCells reserved, (entry b z : ℝ)) -
        ((1 + (centralFreeMain (by omega) reserved).card +
          (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
            centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ 3 * η ∧
      centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue =
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
          ((∑ z ∈ unreservedDiagonalCells reserved, (entry b z : ℝ)) -
            ((1 + (centralFreeMain (by omega) reserved).card +
              (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
                centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) /
                  ((actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        3 * η / ((actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeMain (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤ 2 * η ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤ (201 / 100) * η ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  have hp : 0 < n := by omega
  let unused := actualUnusedPool a reserved
  let X : Finset (Cell n) := {centralCell n hp}
  let Y := centralFreeMain hp reserved
  let Z := centralFreeAnti hp reserved
  have hcount := actualUnusedPool_card n a reserved
  have hN : 3 * n * n ≤ 4 * unused.card := by
    dsimp [unused]
    nlinarith [hcount]
  obtain ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, himX, himY, himZ, hfixed,
    hcentral, hleft, htotal, hdiag₁, hdiag₂, hpool, hinj⟩ :=
    central_place_odd_diagonals a unused reserved c η hη hn hodd hcenter hN hmean
      hlow hhigh (actualUnusedPool_avoids a reserved)
  have hpartition : X ∪ Y ∪ Z = unreservedDiagonalCells reserved :=
    unreservedDiagonalCells_partition hp hodd reserved hcenter
  have himage : (unreservedDiagonalCells reserved).image (entry b) = (A ∪ B ∪ C).image Subtype.val := by
    rw [← hpartition, Finset.image_union, Finset.image_union, himX, himY, himZ,
      Finset.image_union, Finset.image_union]
  have hremain := actualUnusedPool_after_placement a b reserved (unreservedDiagonalCells reserved)
    (A ∪ B ∪ C) hfixed himage
  have hsdiff : unused \ (A ∪ B ∪ C) = ((unused \ A) \ B) \ C := by
    ext v
    simp [and_assoc, and_comm, and_left_comm]
  rw [hsdiff] at hremain
  have hABCsub : A ∪ B ∪ C ⊆ unused := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact hA hv
      · exact (Finset.mem_sdiff.mp (hB hv)).1
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hC hv)).1).1
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp (hB hw)).2 hv
  have hAC : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hC hw)).1).2 hv
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp (hC hw)).2 hv
  have hcard : (A ∪ B ∪ C).card = 1 + Y.card + Z.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint hAB, hcA, hcB, hcC]
  have hn2 : 2 ≤ n * n := by nlinarith
  have hK : 0 < n * n / 2 := Nat.div_pos hn2 (by decide)
  have hpos : 0 < (unused \ (A ∪ B ∪ C)).card := by
    rw [hsdiff]
    omega
  have hmean_update := central_entries_actual_mean_update unused (A ∪ B ∪ C)
    centralPoolValue hABCsub hpos
  have hsum := finite_population_sum b (unreservedDiagonalCells reserved) (A ∪ B ∪ C) himage
  rw [hcard, ← hsum, hsdiff, ← hremain] at hmean_update
  have htot : |(∑ z ∈ unreservedDiagonalCells reserved, (entry b z : ℝ)) -
      ((1 + Y.card + Z.card : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue| ≤ 3 * η := by
    rw [← hpartition]
    exact htotal
  have hden : (0 : ℝ) < ((actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) := by
    rw [hremain]
    exact_mod_cast (show 0 < (((unused \ A) \ B) \ C).card by omega)
  have hshift : |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      centralEntriesMean unused centralPoolValue| ≤
        3 * η / ((actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) := by
    rw [hmean_update]
    have heq : centralEntriesMean unused centralPoolValue -
          ((∑ z ∈ unreservedDiagonalCells reserved, (entry b z : ℝ)) -
            ((1 + Y.card + Z.card : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue) /
              ((actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) -
            centralEntriesMean unused centralPoolValue =
        -(((∑ z ∈ unreservedDiagonalCells reserved, (entry b z : ℝ)) -
            ((1 + Y.card + Z.card : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue) /
              ((actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ)) := by ring
    rw [heq, abs_neg, abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right htot hden.le
  refine ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, hfixed, ?_, hremain, ?_, htot, hmean_update, hshift,
    hdiag₁, hdiag₂, hpool, hinj⟩
  · intro z hz
    apply hcentral z
    rw [hpartition]
    exact hz
  · rw [hremain]
    exact hleft

end
end Sude
