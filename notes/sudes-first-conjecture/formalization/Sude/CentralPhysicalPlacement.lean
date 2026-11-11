import Sude.CentralDiagonalSelection
import Sude.FinitePopulationPlacement

/-! Place the three centrally selected populations in actual disjoint cells. -/
namespace Sude
noncomputable section

def centralPoolValue {n : ℕ} (v : pool n) : ℝ := (v.val : ℝ)

theorem centralPoolValue_injective {n : ℕ} : Function.Injective (centralPoolValue (n := n)) := by
  intro x y h
  apply Subtype.ext
  exact Nat.cast_injective h

/-- An exact cell-value image equality transports the sum without losing
multiplicity, because both the placement and subtype coercion are injective. -/
theorem finite_population_sum {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (cells : Finset (Cell n)) (values : Finset (pool n))
    (himage : cells.image (entry a) = values.image Subtype.val) :
    (∑ c ∈ cells, (entry a c : ℝ)) = ∑ v ∈ values, centralPoolValue v := by
  classical
  have h := congrArg (fun s : Finset ℕ => ∑ x ∈ s, (x : ℝ)) himage
  rw [Finset.sum_image (entry_injective a).injOn,
    Finset.sum_image Subtype.val_injective.injOn] at h
  exact h

/-- Given the actual unused pool and three disjoint free cell groups of the
right sizes, place the CC2 selections and preserve all previously reserved
cells. The same center group occurs in both displayed diagonal sums. The
caller must identify these groups with its actual free diagonal cells and
prove the central-stock inequalities; this does not fill other empty cells. -/
theorem central_select_and_place {n : ℕ} (a : Cell n ≃ Fin (n * n))
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
      |(∑ z ∈ X ∪ Y, (entry b z : ℝ)) -
        ((1 + q₁ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue| ≤ 2 * η ∧
      |(∑ z ∈ X ∪ Z, (entry b z : ℝ)) -
        ((1 + q₂ : ℕ) : ℝ) * centralEntriesMean unused centralPoolValue| ≤ (201 / 100) * η ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  obtain ⟨A, B, C, hA, hB, hC, hcA, hcB, hcC, hcentral, hleft, htotal, hdiag₁, hdiag₂⟩ :=
    central_source_batches_with_diagonal_errors unused centralPoolValue centralPoolValue_injective.injOn
      n q₁ q₂ c η hη hn hN hq₁ hq₂ hmean hlow hhigh
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
  have hABC : A ∪ B ∪ C ⊆ unused := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact hA hv
      · exact (Finset.mem_sdiff.mp (hB hv)).1
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp (hC hv)).1).1
  obtain ⟨b, himX, himY, himZ, hfixed, hpool, hinj⟩ :=
    place_three_finite_populations a X Y Z A B C reserved (hcA.trans hX.symm)
      (hcB.trans hY.symm) (hcC.trans hZ.symm) hXR hYR hZR hXY hXZ hYZ hAB hAC hBC
      (fun v hv z hz => havoid v (hABC hv) z hz)
  have hsX := finite_population_sum b X A himX
  have hsY := finite_population_sum b Y B himY
  have hsZ := finite_population_sum b Z C himZ
  have hXY_Z : Disjoint (X ∪ Y) Z := Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
  have hAB_C : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  have hsum₁ : (∑ z ∈ X ∪ Y, (entry b z : ℝ)) = ∑ v ∈ A ∪ B, centralPoolValue v := by
    rw [Finset.sum_union hXY, Finset.sum_union hAB, hsX, hsY]
  have hsum₂ : (∑ z ∈ X ∪ Z, (entry b z : ℝ)) = ∑ v ∈ A ∪ C, centralPoolValue v := by
    rw [Finset.sum_union hXZ, Finset.sum_union hAC, hsX, hsZ]
  have hsum : (∑ z ∈ X ∪ Y ∪ Z, (entry b z : ℝ)) = ∑ v ∈ A ∪ B ∪ C, centralPoolValue v := by
    rw [Finset.sum_union hXY_Z, Finset.sum_union hXY,
      Finset.sum_union hAB_C, Finset.sum_union hAB, hsX, hsY, hsZ]
  refine ⟨b, A, B, C, hA, hB, hC, hcA, hcB, hcC, himX, himY, himZ, hfixed, ?_,
    hleft, ?_, ?_, ?_, hpool, hinj⟩
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · have hm : entry b z ∈ A.image Subtype.val := by rw [← himX]; exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
        obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hm
        have hv' := hcentral v (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
        simpa [centralPoolValue, heq] using hv'
      · have hm : entry b z ∈ B.image Subtype.val := by rw [← himY]; exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
        obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hm
        have hv' := hcentral v (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
        simpa [centralPoolValue, heq] using hv'
    · have hm : entry b z ∈ C.image Subtype.val := by rw [← himZ]; exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hm
      have hv' := hcentral v (Finset.mem_union_right _ hv)
      simpa [centralPoolValue, heq] using hv'
  · rw [hsum]
    exact htotal
  · rw [hsum₁]
    exact hdiag₁
  · rw [hsum₂]
    exact hdiag₂

end
end Sude
