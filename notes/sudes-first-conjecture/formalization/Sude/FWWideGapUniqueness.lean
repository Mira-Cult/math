import Sude.FWWidePhysicalGrid

/-! Reconcile two wide-stage gap choices on the same actual square and edge.
This does not supply switch separation, flows, or line corrections. -/
namespace Sude
noncomputable section

/-- Two gaps satisfying the same physical pair equations on both networks
are identical at every stage. -/
theorem fw_same_square_wide_gaps_unique {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n*n)) (k : Fin 3) (e : Fin n)
    (wide₁ wide₂ : Fin (3 * (n / 450)) → ℕ)
    (h₁ : ∀ j network,
      entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
      entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + wide₁ j)
    (h₂ : ∀ j network,
      entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
      entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + wide₂ j) :
    wide₁ = wide₂ := by
  funext j
  exact Nat.add_left_cancel ((h₁ j false).symm.trans (h₂ j false))

/-- The independently supplied row and column grid witnesses at one edge
can use a single wide-gap function on the same square and radius. Both
original grids and their numerical wide-gap data are preserved. -/
theorem fw_reconcile_physical_wide_edge_grids {α : Type*} [DecidableEq α] {n L : ℕ}
    (X : ℝ) (S : Finset α) (rowGap colGap : α → ℕ) (R : ℕ)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3)
    (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n*n)) (k : Fin 3) (e : Fin n)
    (hrow : ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + wide j) ∧
        (2 / 3 : ℝ) * X ≤ (wide j : ℝ) ∧ (wide j : ℝ) < X) ∧
      CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim rowGap wide) (R + ∑ j, wide j) ∧
      2 ∣ R + ∑ j, wide j ∧ (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide j : ℝ))
    (hcol : ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + wide j) ∧
        (2 / 3 : ℝ) * X ≤ (wide j : ℝ) ∧ (wide j : ℝ) < X) ∧
      CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim colGap wide) (R + ∑ j, wide j) ∧
      2 ∣ R + ∑ j, wide j ∧ (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide j : ℝ)) :
    ∃ wide : Fin (3 * (n / 450)) → ℕ,
      (∀ j, 0 < wide j ∧ 2 ∣ wide j ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
          entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + wide j) ∧
        (2 / 3 : ℝ) * X ≤ (wide j : ℝ) ∧ (wide j : ℝ) < X) ∧
      CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim rowGap wide) (R + ∑ j, wide j) ∧
      CompleteEvenGrid (S.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim colGap wide) (R + ∑ j, wide j) ∧
      2 ∣ R + ∑ j, wide j ∧ (2 : ℝ) * (n / 450 : ℕ) * X ≤ ∑ j, (wide j : ℝ) := by
  obtain ⟨wide₁, hw₁, hgrid₁, heven, hsum⟩ := hrow
  obtain ⟨wide₂, hw₂, hgrid₂, _, _⟩ := hcol
  have heq : wide₁ = wide₂ := fw_same_square_wide_gaps_unique hwide hs choice rows cols hr hc a k e
    wide₁ wide₂ (fun j network => (hw₁ j).2.2.1 network) (fun j network => (hw₂ j).2.2.1 network)
  subst wide₂
  exact ⟨wide₁, hw₁, hgrid₁, hgrid₂, heven, hsum⟩

end
end Sude
