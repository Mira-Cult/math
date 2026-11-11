import Sude.Placement

/-! Place a finite set of distinct pool entries in a finite set of cells. -/
namespace Sude
noncomputable section

/-- Equal-cardinality sets of pool entries and cells admit an exact physical
placement, preserving every prior reservation. Both the selected cells and
selected values must avoid the reservation. -/
theorem place_finite_population {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (cells : Finset (Cell n)) (values : Finset (pool n)) (reserved : Finset (Cell n))
    (hcard : values.card = cells.card) (hdisj : Disjoint cells reserved)
    (havoid : ∀ v ∈ values, ∀ c ∈ reserved, v.val ≠ entry a c) :
    ∃ b : Cell n ≃ Fin (n * n),
      cells.image (entry b) = values.image Subtype.val ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  have hc : Fintype.card {v // v ∈ values} = Fintype.card {c // c ∈ cells} := by
    simpa using hcard
  let e : {v // v ∈ values} ≃ {c // c ∈ cells} := Fintype.equivOfCardEq hc
  let cell : {v // v ∈ values} → Cell n := fun v => (e v).val
  let val : {v // v ∈ values} → pool n := Subtype.val
  have hcell : Function.Injective cell := by
    intro x y h
    apply e.injective
    exact Subtype.ext h
  have hval : Function.Injective val := Subtype.val_injective
  have hnew : ∀ v, cell v ∉ reserved := by
    intro v hv
    exact Finset.disjoint_left.mp hdisj (e v).property hv
  have hav : ∀ v c, c ∈ reserved → (val v).val ≠ entry a c := by
    intro v c hc'
    exact havoid v.val v.property c hc'
  obtain ⟨b, hplaced, hfixed⟩ :=
    place_distinct_pool_entries_preserving a cell val reserved hcell hval hnew hav
  refine ⟨b, ?_, hfixed, entry_range _, entry_injective _⟩
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc', rfl⟩ := Finset.mem_image.mp hx
    let v := e.symm ⟨c, hc'⟩
    have he : cell v = c := by simp [cell, v]
    refine Finset.mem_image.mpr ⟨v.val, v.property, ?_⟩
    simpa [he, val] using (hplaced v).symm
  · intro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    let w : {v // v ∈ values} := ⟨v, hv⟩
    refine Finset.mem_image.mpr ⟨cell w, (e w).property, ?_⟩
    simpa [val, w] using hplaced w

/-- An installed population cannot contain a value from a disjoint family. -/
theorem disjoint_population_avoids {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (cells : Finset (Cell n)) (installed other : Finset (pool n))
    (himage : cells.image (entry a) = installed.image Subtype.val)
    (hdisj : Disjoint other installed) :
    ∀ v ∈ other, ∀ c ∈ cells, v.val ≠ entry a c := by
  intro v hv c hc heq
  have hm : entry a c ∈ installed.image Subtype.val := by
    rw [← himage]
    exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  obtain ⟨w, hw, hwval⟩ := Finset.mem_image.mp hm
  have hvw : v = w := Subtype.ext (heq.trans hwval.symm)
  exact Finset.disjoint_left.mp hdisj hv (hvw ▸ hw)

/-- Install three disjoint families into three disjoint cell sets, retaining
each family's exact image and all prior reserved entries. -/
theorem place_three_finite_populations {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (X Y Z : Finset (Cell n)) (A B C : Finset (pool n)) (reserved : Finset (Cell n))
    (hX : A.card = X.card) (hY : B.card = Y.card) (hZ : C.card = Z.card)
    (hXR : Disjoint X reserved) (hYR : Disjoint Y reserved) (hZR : Disjoint Z reserved)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (havoid : ∀ v ∈ A ∪ B ∪ C, ∀ c ∈ reserved, v.val ≠ entry a c) :
    ∃ b : Cell n ≃ Fin (n * n),
      X.image (entry b) = A.image Subtype.val ∧
      Y.image (entry b) = B.image Subtype.val ∧
      Z.image (entry b) = C.image Subtype.val ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  have havA : ∀ v ∈ A, ∀ c ∈ reserved, v.val ≠ entry a c := by
    intro v hv c hc
    exact havoid v (Finset.mem_union_left _ (Finset.mem_union_left _ hv)) c hc
  obtain ⟨a₁, himA, hfix₁, _, _⟩ := place_finite_population a X A reserved hX hXR havA
  have havB : ∀ v ∈ B, ∀ c ∈ reserved ∪ X, v.val ≠ entry a₁ c := by
    intro v hv c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rw [hfix₁ c hc]
      exact havoid v (Finset.mem_union_left _ (Finset.mem_union_right _ hv)) c hc
    · exact disjoint_population_avoids a₁ X A B himA hAB.symm v hv c hc
  obtain ⟨a₂, himB, hfix₂, _, _⟩ := place_finite_population a₁ Y B (reserved ∪ X) hY
    (Finset.disjoint_union_right.mpr ⟨hYR, hXY.symm⟩) havB
  have himA₂ : X.image (entry a₂) = A.image Subtype.val := by
    calc
      X.image (entry a₂) = X.image (entry a₁) := Finset.image_congr (fun c hc =>
        hfix₂ c (Finset.mem_union_right _ hc))
      _ = A.image Subtype.val := himA
  have havC : ∀ v ∈ C, ∀ c ∈ (reserved ∪ X) ∪ Y, v.val ≠ entry a₂ c := by
    intro v hv c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · rcases Finset.mem_union.mp hc with hcR | hcX
      · rw [hfix₂ c (Finset.mem_union_left _ hcR), hfix₁ c hcR]
        exact havoid v (Finset.mem_union_right _ hv) c hcR
      · exact disjoint_population_avoids a₂ X A C himA₂ hAC.symm v hv c hcX
    · exact disjoint_population_avoids a₂ Y B C himB hBC.symm v hv c hc
  obtain ⟨b, himC, hfix₃, hpool, hinj⟩ := place_finite_population a₂ Z C ((reserved ∪ X) ∪ Y) hZ
    (Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨hZR, hXZ.symm⟩, hYZ.symm⟩) havC
  refine ⟨b, ?_, ?_, himC, ?_, hpool, hinj⟩
  · calc
      X.image (entry b) = X.image (entry a₂) := Finset.image_congr (fun c hc =>
        hfix₃ c (Finset.mem_union_left _ (Finset.mem_union_right _ hc)))
      _ = A.image Subtype.val := himA₂
  · calc
      Y.image (entry b) = Y.image (entry a₂) := Finset.image_congr (fun c hc =>
        hfix₃ c (Finset.mem_union_right _ hc))
      _ = B.image Subtype.val := himB
  · intro c hc
    exact (hfix₃ c (Finset.mem_union_left _ (Finset.mem_union_left _ hc))).trans
      ((hfix₂ c (Finset.mem_union_left _ hc)).trans (hfix₁ c hc))

end
end Sude
