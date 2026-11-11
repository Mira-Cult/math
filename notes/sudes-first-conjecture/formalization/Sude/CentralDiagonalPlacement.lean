import Sude.CentralPhysicalPlacement

/-! The selected central batches placed on the actual labelled diagonals. -/
namespace Sude
noncomputable section

theorem mainSum_real_cells {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    (mainSum a : ℝ) = ∑ z ∈ mainCells n, (entry a z : ℝ) := by
  classical
  unfold mainCells mainSum
  rw [Finset.sum_image (by intro i hi j hj h; exact congrArg Prod.fst h)]
  simp

theorem antiSum_real_cells {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    (antiSum a : ℝ) = ∑ z ∈ antiCells n, (entry a z : ℝ) := by
  classical
  unfold antiCells antiSum
  rw [Finset.sum_image (by intro i hi j hj h; exact congrArg Prod.fst h)]
  simp

/-- Split an actual line into its previously fixed and newly assigned cells. -/
theorem central_line_fixed_parts {n : ℕ} (a b : Cell n ≃ Fin (n * n))
    (line reserved : Finset (Cell n))
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z) :
    (∑ z ∈ line, (entry b z : ℝ)) =
      (∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        ∑ z ∈ line \ reserved, (entry b z : ℝ) := by
  have hsum : (∑ z ∈ line ∩ reserved, (entry b z : ℝ)) =
      ∑ z ∈ line ∩ reserved, (entry a z : ℝ) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hfixed z (Finset.mem_inter.mp hz).2]
  calc
    (∑ z ∈ line, (entry b z : ℝ)) =
        ∑ z ∈ (line \ reserved) ∪ (line ∩ reserved), (entry b z : ℝ) := by
          rw [Finset.sdiff_union_inter]
    _ = (∑ z ∈ line \ reserved, (entry b z : ℝ)) +
        ∑ z ∈ line ∩ reserved, (entry b z : ℝ) :=
      Finset.sum_union (Finset.disjoint_sdiff_inter line reserved)
    _ = _ := by rw [hsum]; ring

/-- Install the central batches in the actual free main and antidiagonal
cells, counting their common singleton once. The output bounds the full
labelled diagonal sums around their original unused-pool expectations.
The exact unused stock counts and the cell partition are still inputs. -/
theorem central_place_actual_diagonals {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (unused : Finset (pool n)) (reserved X Y Z : Finset (Cell n))
    (q₁ q₂ : ℕ) (c η : ℝ) (hη : 0 < η) (hn : 20 ≤ n)
    (hN : 3 * n * n ≤ 4 * unused.card) (hq₁ : q₁ ≤ n - 1) (hq₂ : q₂ ≤ n - 1)
    (hmean : |centralEntriesMean unused centralPoolValue - c| ≤ η / 4)
    (hlow : 1 + q₁ + q₂ ≤
      (unused.filter (fun v => c - η < centralPoolValue v ∧ centralPoolValue v ≤ c - η / 2)).card)
    (hhigh : 1 + q₁ + q₂ ≤
      (unused.filter (fun v => c + η / 2 < centralPoolValue v ∧ centralPoolValue v ≤ c + η)).card)
    (hX : X.card = 1) (hY : Y.card = q₁) (hZ : Z.card = q₂)
    (hXR : Disjoint X reserved) (hYR : Disjoint Y reserved) (hZR : Disjoint Z reserved)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hmain : X ∪ Y = mainCells n \ reserved) (hanti : X ∪ Z = antiCells n \ reserved)
    (havoid : ∀ v ∈ unused, ∀ z ∈ reserved, v.val ≠ entry a z) :
    ∃ (b : Cell n ≃ Fin (n * n)) (A B C : Finset (pool n)),
      A ⊆ unused ∧ B ⊆ unused \ A ∧ C ⊆ (unused \ A) \ B ∧
      A.card = 1 ∧ B.card = q₁ ∧ C.card = q₂ ∧
      X.image (entry b) = A.image Subtype.val ∧
      Y.image (entry b) = B.image Subtype.val ∧
      Z.image (entry b) = C.image Subtype.val ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ z ∈ X ∪ Y ∪ Z, |(entry b z : ℝ) - c| ≤ η) ∧
      n * n / 2 ≤ (((unused \ A) \ B) \ C).card ∧
      |(∑ z ∈ X ∪ Y ∪ Z, (entry b z : ℝ)) -
        ((1 + q₁ + q₂ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue| ≤ 3 * η ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + q₁ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue)| ≤ 2 * η ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + q₂ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue)| ≤ (201 / 100) * η ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, himX, himY, himZ, hfixed,
    hcentral, hleft, htotal, hdiag₁, hdiag₂, hpool, hinj⟩ :=
    central_select_and_place a unused reserved X Y Z q₁ q₂ c η hη hn hN hq₁ hq₂ hmean
      hlow hhigh hX hY hZ hXR hYR hZR hXY hXZ hYZ havoid
  have hm := central_line_fixed_parts a b (mainCells n) reserved hfixed
  have ha := central_line_fixed_parts a b (antiCells n) reserved hfixed
  rw [← hmain] at hm
  rw [← hanti] at ha
  have hm' : (mainSum b : ℝ) = (∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
      ∑ z ∈ X ∪ Y, (entry b z : ℝ) := by rw [mainSum_real_cells]; exact hm
  have ha' : (antiSum b : ℝ) = (∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
      ∑ z ∈ X ∪ Z, (entry b z : ℝ) := by rw [antiSum_real_cells]; exact ha
  refine ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, himX, himY, himZ, hfixed,
    hcentral, hleft, htotal, ?_, ?_, hpool, hinj⟩
  · rw [hm']
    have heq : ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
          ∑ z ∈ X ∪ Y, (entry b z : ℝ)) -
        ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
          ((1 + q₁ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue) =
        (∑ z ∈ X ∪ Y, (entry b z : ℝ)) -
          ((1 + q₁ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue := by ring
    rw [heq]
    exact hdiag₁
  · rw [ha']
    have heq : ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
          ∑ z ∈ X ∪ Z, (entry b z : ℝ)) -
        ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
          ((1 + q₂ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue) =
        (∑ z ∈ X ∪ Z, (entry b z : ℝ)) -
          ((1 + q₂ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue := by ring
    rw [heq]
    exact hdiag₂

end
end Sude
