import Sude.FWJointLayerPacking
import Sude.NetworkSwitches

/-! Combine actual oriented physical layer gaps. This module assumes the
family-level orderings; it neither selects witnesses nor proves flow bounds. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

def fwRowsOriented {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n)) : Prop :=
  ∀ i : Fin layers.length, ∀ e : Fin n,
    entry a (e, (layers.get i).2 e) ≤ entry a ((layers.get i).1 e, (layers.get i).2 e)

def fwColumnsOriented {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n)) : Prop :=
  ∀ i : Fin layers.length, ∀ e : Fin n,
    entry a ((layers.get i).2 e, e) ≤ entry a ((layers.get i).2 e, (layers.get i).1 e)

/-- Layer-by-layer orientation survives list concatenation. -/
theorem fw_rows_oriented_append {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (xs ys : List (LayerPacking.Layer n))
    (hx : fwRowsOriented a xs) (hy : fwRowsOriented a ys) :
    fwRowsOriented a (xs ++ ys) := by
  intro i e
  have hm := List.get_mem (xs ++ ys) i
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    simpa only [hj] using hx j e
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    simpa only [hj] using hy j e

/-- The analogous orientation result for transposed column layers. -/
theorem fw_columns_oriented_append {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (xs ys : List (LayerPacking.Layer n))
    (hx : fwColumnsOriented a xs) (hy : fwColumnsOriented a ys) :
    fwColumnsOriented a (xs ++ ys) := by
  intro i e
  have hm := List.get_mem (xs ++ ys) i
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    simpa only [hj] using hx j e
  · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
    simpa only [hj] using hy j e

/-- The gap of a row layer is the actual difference of its two entries. -/
def fwPhysicalRowLayerGap {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n)) (i : Fin layers.length) (e : Fin n) : ℕ :=
  entry a ((layers.get i).1 e, (layers.get i).2 e) - entry a (e, (layers.get i).2 e)

/-- The gap of a column layer is measured on the original square. -/
def fwPhysicalColumnLayerGap {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n)) (i : Fin layers.length) (e : Fin n) : ℕ :=
  entry a ((layers.get i).2 e, (layers.get i).1 e) - entry a ((layers.get i).2 e, e)

theorem fw_row_physical_gap_equation {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n)) (h : fwRowsOriented a layers)
    (i : Fin layers.length) (e : Fin n) :
    entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + fwPhysicalRowLayerGap a layers i e := by
  exact (Nat.add_sub_of_le (h i e)).symm

theorem fw_column_physical_gap_equation {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (layers : List (LayerPacking.Layer n)) (h : fwColumnsOriented a layers)
    (i : Fin layers.length) (e : Fin n) :
    entry a ((layers.get i).2 e, (layers.get i).1 e) =
      entry a ((layers.get i).2 e, e) + fwPhysicalColumnLayerGap a layers i e := by
  exact (Nat.add_sub_of_le (h i e)).symm

/-- Combine four physical row and column families, retaining the original
family order used by the joint packing. -/
theorem fw_four_family_physical_gap_equations {n : ℕ}
    (a : Cell n ≃ Fin (n*n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : fwRowsOriented a br) (hbc : fwColumnsOriented a bc)
    (hsr : fwRowsOriented a sr) (hsc : fwColumnsOriented a sc)
    (hwr : fwRowsOriented a wr) (hwc : fwColumnsOriented a wc)
    (hgr : fwRowsOriented a gr) (hgc : fwColumnsOriented a gc) :
    let rows := ((br ++ sr) ++ wr) ++ gr
    let cols := ((bc ++ sc) ++ wc) ++ gc
    (∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + fwPhysicalRowLayerGap a rows i e) ∧
    (∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + fwPhysicalColumnLayerGap a cols i e) := by
  dsimp only
  have hr := fw_rows_oriented_append a _ _ (fw_rows_oriented_append a _ _
    (fw_rows_oriented_append a br sr hbr hsr) hwr) hgr
  have hc := fw_columns_oriented_append a _ _ (fw_columns_oriented_append a _ _
    (fw_columns_oriented_append a bc sc hbc hsc) hwc) hgc
  exact ⟨fw_row_physical_gap_equation a _ hr, fw_column_physical_gap_equation a _ hc⟩

end
end Sude
