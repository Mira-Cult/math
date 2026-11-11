import Sude.CentralDiagonalGeometry

/-! Instantiate central diagonal placement with the actual odd-square geometry. -/
namespace Sude
noncomputable section

/-- Under the explicit CC central-stock conditions, fill every unreserved
diagonal cell of an odd square. The center is placed exactly once; the two
labelled sums obey CC11 relative to the original unused-pool expectation.
The off-diagonal completion and the stock-count estimates remain separate. -/
theorem central_place_odd_diagonals {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (unused : Finset (pool n)) (reserved : Finset (Cell n)) (c η : ℝ)
    (hη : 0 < η) (hn : 20 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hN : 3 * n * n ≤ 4 * unused.card)
    (hmean : |centralEntriesMean unused centralPoolValue - c| ≤ η / 4)
    (hlow : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      (unused.filter (fun v => c - η < centralPoolValue v ∧ centralPoolValue v ≤ c - η / 2)).card)
    (hhigh : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      (unused.filter (fun v => c + η / 2 < centralPoolValue v ∧ centralPoolValue v ≤ c + η)).card)
    (havoid : ∀ v ∈ unused, ∀ z ∈ reserved, v.val ≠ entry a z) :
    ∃ (b : Cell n ≃ Fin (n * n)) (A B C : Finset (pool n)),
      A ⊆ unused ∧ B ⊆ unused \ A ∧ C ⊆ (unused \ A) \ B ∧
      A.card = 1 ∧ B.card = (centralFreeMain (by omega) reserved).card ∧
      C.card = (centralFreeAnti (by omega) reserved).card ∧
      ({centralCell n (by omega)} : Finset (Cell n)).image (entry b) = A.image Subtype.val ∧
      (centralFreeMain (by omega) reserved).image (entry b) = B.image Subtype.val ∧
      (centralFreeAnti (by omega) reserved).image (entry b) = C.image Subtype.val ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ z ∈ ({centralCell n (by omega)} : Finset (Cell n)) ∪
          centralFreeMain (by omega) reserved ∪ centralFreeAnti (by omega) reserved,
        |(entry b z : ℝ) - c| ≤ η) ∧
      n * n / 2 ≤ (((unused \ A) \ B) \ C).card ∧
      |(∑ z ∈ ({centralCell n (by omega)} : Finset (Cell n)) ∪
          centralFreeMain (by omega) reserved ∪ centralFreeAnti (by omega) reserved,
          (entry b z : ℝ)) -
        ((1 + (centralFreeMain (by omega) reserved).card +
          (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
            centralEntriesMean unused centralPoolValue| ≤ 3 * η ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeMain (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean unused centralPoolValue)| ≤ 2 * η ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean unused centralPoolValue)| ≤ (201 / 100) * η ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  have hp : 0 < n := by omega
  let X : Finset (Cell n) := {centralCell n hp}
  let Y := centralFreeMain hp reserved
  let Z := centralFreeAnti hp reserved
  obtain ⟨hX, hY, hZ, hXR, hYR, hZR, hXY, hXZ, hYZ, hmain, hanti⟩ :=
    central_free_diagonal_geometry hp hodd reserved hcenter
  obtain ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, himX, himY, himZ, hfixed,
    hcentral, hleft, htotal, hdiag₁, hdiag₂, hpool, hinj⟩ :=
    central_place_actual_diagonals a unused reserved X Y Z Y.card Z.card c η hη hn hN hY hZ
      hmean hlow hhigh hX rfl rfl hXR hYR hZR hXY hXZ hYZ hmain hanti havoid
  exact ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, himX, himY, himZ, hfixed, hcentral, hleft, htotal,
    hdiag₁, hdiag₂, hpool, hinj⟩

end
end Sude
