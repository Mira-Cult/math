import Sude.FWWideGapUniqueness

/-! Reconcile the two supplied physical wide-grid witnesses at every edge.
All choices and numerical bounds remain conditional on the supplied input. -/
namespace Sude
noncomputable section

/-- From independently supplied row/column witnesses at each edge, choose one
family whose physical equations, both grids and numerical bounds hold for that
same edge. This constructs no physical placement, reference square or invoice. -/
theorem fw_global_reconcile_physical_wide_grids {α : Type*} [DecidableEq α] {n L : ℕ}
    (X : ℝ) (S : Finset α)
    (rowGap colGap : (Fin 3 × Fin n) → α → ℕ) (R : (Fin 3 × Fin n) → ℕ)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n*n))
    (hgrid : ∀ (edge : Fin 3 × Fin n) (network : Bool),
      ∃ wide : Fin (3 * (n / 450)) → ℕ,
        (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
          (∀ sideNetwork : Bool,
            entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 sideNetwork true)) =
            entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 sideNetwork false)) + wide j) ∧
          (2 / 3 : ℝ) * X ≤ (wide j : ℝ) ∧ (wide j : ℝ) < X) ∧
        CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
          (Sum.elim (if network then colGap edge else rowGap edge) wide) (R edge + ∑ j, wide j) ∧
        2 ∣ R edge + ∑ j, wide j ∧
        (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide j : ℝ)) :
    ∃ wide : (Fin 3 × Fin n) → Fin (3 * (n / 450)) → ℕ,
      ∀ edge,
        (∀ j, 0 < wide edge j ∧ 2 ∣ wide edge j ∧
          (∀ network : Bool,
            entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
            entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide edge j) ∧
          (2 / 3 : ℝ) * X ≤ (wide edge j : ℝ) ∧ (wide edge j : ℝ) < X) ∧
        CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
          (Sum.elim (rowGap edge) (wide edge)) (R edge + ∑ j, wide edge j) ∧
        CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
          (Sum.elim (colGap edge) (wide edge)) (R edge + ∑ j, wide edge j) ∧
        2 ∣ R edge + ∑ j, wide edge j ∧
        (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide edge j : ℝ) := by
  classical
  have h : ∀ edge : Fin 3 × Fin n, ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network true)) =
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j edge.1 edge.2 network false)) + wide j) ∧
        (2 / 3 : ℝ) * X ≤ (wide j : ℝ) ∧ (wide j : ℝ) < X) ∧
      CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim (rowGap edge) wide) (R edge + ∑ j, wide j) ∧
      CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim (colGap edge) wide) (R edge + ∑ j, wide j) ∧
      2 ∣ R edge + ∑ j, wide j ∧
      (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide j : ℝ) := by
    intro edge
    exact fw_reconcile_physical_wide_edge_grids X S (rowGap edge) (colGap edge) (R edge)
      hwide hs choice rows cols hr hc a edge.1 edge.2 (by simpa using hgrid edge false)
      (by simpa using hgrid edge true)
  choose wide hw using h
  exact ⟨wide, hw⟩

end
end Sude
