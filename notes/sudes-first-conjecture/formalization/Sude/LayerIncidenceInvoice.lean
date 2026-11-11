import Sude.LayerPacking

/-! Exact squared midpoint-incidence weights for one physical network layer. -/
namespace Sude.LayerPacking
noncomputable section

/-- The number of the pair's two physical cells lying on a given row. -/
def layerRowWeight {n : ℕ} (π f : Equiv.Perm (Fin n)) (r i : Fin n) : ℝ :=
  (if (layerCell π f (i, false)).1 = r then 1 else 0) +
    (if (layerCell π f (i, true)).1 = r then 1 else 0)

/-- The number of the pair's two physical cells lying on a given column. -/
def layerColumnWeight {n : ℕ} (π f : Equiv.Perm (Fin n)) (c i : Fin n) : ℝ :=
  (if (layerCell π f (i, false)).2 = c then 1 else 0) +
    (if (layerCell π f (i, true)).2 = c then 1 else 0)

/-- A row meets the two distinct edge slots incident with that row. -/
theorem layerRowWeight_eq {n : ℕ} (π f : Equiv.Perm (Fin n)) (r i : Fin n) :
    layerRowWeight π f r i =
      (if i = r then 1 else 0) + (if i = π.symm r then 1 else 0) := by
  simp [layerRowWeight, layerCell, ← Equiv.eq_symm_apply π]

/-- A column meets both endpoints of the unique pair in that column. -/
theorem layerColumnWeight_eq {n : ℕ} (π f : Equiv.Perm (Fin n)) (c i : Fin n) :
    layerColumnWeight π f c i = if i = f.symm c then 2 else 0 := by
  simp [layerColumnWeight, layerCell, ← Equiv.eq_symm_apply f]
  split <;> norm_num

/-- Each row layer has squared-weight invoice exactly two. -/
theorem layerRowWeight_sq_sum {n : ℕ} (π f : Equiv.Perm (Fin n))
    (hderange : ∀ i, π i ≠ i) (r : Fin n) :
    ∑ i, (layerRowWeight π f r i) ^ 2 = 2 := by
  have hne : r ≠ π.symm r := by
    intro h
    apply hderange r
    simpa using congrArg π h
  have hp : ∀ i, (layerRowWeight π f r i) ^ 2 =
      (if i = r then (1 : ℝ) else 0) + (if i = π.symm r then 1 else 0) := by
    intro i
    rw [layerRowWeight_eq]
    by_cases h1 : i = r <;> by_cases h2 : i = π.symm r <;> simp_all
  simp only [hp, Finset.sum_add_distrib]
  simp
  norm_num

/-- Each column layer has squared-weight invoice exactly four. -/
theorem layerColumnWeight_sq_sum {n : ℕ} (π f : Equiv.Perm (Fin n)) (c : Fin n) :
    ∑ i, (layerColumnWeight π f c i) ^ 2 = 4 := by
  simp [layerColumnWeight_eq]
  norm_num

/-- A row in a transposed layer has the original column's pair weights. -/
theorem transposedLayerRowWeight_eq {n : ℕ} (π f : Equiv.Perm (Fin n))
    (r i : Fin n) :
    ((if (layerCell π f (i, false)).swap.1 = r then 1 else 0) +
      (if (layerCell π f (i, true)).swap.1 = r then 1 else 0) : ℝ) =
        layerColumnWeight π f r i := by
  rfl

/-- In a stage with `s` row layers and `s` transposed column layers,
`d = 2s` gives the source's ordinary `3d` row invoice. -/
theorem ordinary_stage_row_squared_invoice {n s d : ℕ} (hd : d = 2 * s)
    (rowPerm rowColumns colPerm colColumns : Fin s → Equiv.Perm (Fin n))
    (hderange : ∀ j i, rowPerm j i ≠ i) (r : Fin n) :
    (∑ j, ((∑ i, (layerRowWeight (rowPerm j) (rowColumns j) r i) ^ 2) +
      ∑ i, (layerColumnWeight (colPerm j) (colColumns j) r i) ^ 2)) = 3 * (d : ℝ) := by
  have hper : ∀ j : Fin s,
      (∑ i, (layerRowWeight (rowPerm j) (rowColumns j) r i) ^ 2) +
      (∑ i, (layerColumnWeight (colPerm j) (colColumns j) r i) ^ 2) = (6 : ℝ) := by
    intro j
    rw [layerRowWeight_sq_sum _ _ (hderange j), layerColumnWeight_sq_sum]
    norm_num
  simp only [hper, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hd]
  push_cast
  ring

/-- A column in a transposed layer has the original row's pair weights. -/
theorem transposedLayerColumnWeight_eq {n : ℕ} (π f : Equiv.Perm (Fin n))
    (c i : Fin n) :
    ((if (layerCell π f (i, false)).swap.2 = c then 1 else 0) +
      (if (layerCell π f (i, true)).swap.2 = c then 1 else 0) : ℝ) =
        layerRowWeight π f c i := by
  rfl

/-- The same `3d` invoice holds on a column, with the transposed network
contributing the two separate incident slots. -/
theorem ordinary_stage_column_squared_invoice {n s d : ℕ} (hd : d = 2 * s)
    (rowPerm rowColumns colPerm colColumns : Fin s → Equiv.Perm (Fin n))
    (hderange : ∀ j i, colPerm j i ≠ i) (c : Fin n) :
    (∑ j, ((∑ i, (layerColumnWeight (rowPerm j) (rowColumns j) c i) ^ 2) +
      ∑ i, (layerRowWeight (colPerm j) (colColumns j) c i) ^ 2)) = 3 * (d : ℝ) := by
  have hper : ∀ j : Fin s,
      (∑ i, (layerColumnWeight (rowPerm j) (rowColumns j) c i) ^ 2) +
      (∑ i, (layerRowWeight (colPerm j) (colColumns j) c i) ^ 2) = (6 : ℝ) := by
    intro j
    rw [layerColumnWeight_sq_sum, layerRowWeight_sq_sum _ _ (hderange j)]
    norm_num
  simp only [hper, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hd]
  push_cast
  ring

end
end Sude.LayerPacking
