import Sude.PhysicalStageSlots

/-! One injective actual pair-slot indexing for a physical prefix stage. -/
namespace Sude
noncomputable section

/-- Rectangle slots and both ordinary networks in one selected stage. -/
abbrev PrefixStagePair (d layers n : ℕ) :=
  (Fin (4 * d) × Fin 2) ⊕ (Fin 2 × (Fin layers × Fin n))

/-- Map physical stage pair labels into the allocator's `Fin Q` slots. -/
def prefixStagePairSlot {d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    PrefixStagePair d layers n → Fin Q
  | Sum.inl p => prefixDiagonalPairIndex hdiag p
  | Sum.inr p => prefixOrdinaryPairIndex hfit p

/-- Rectangle slots, ordinary slots, and the two networks do not share a
pair slot; every label in a stage identifies a genuine distinct slot. -/
theorem prefixStagePairSlot_injective {d layers n Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q) :
    Function.Injective (prefixStagePairSlot hfit hdiag) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (prefixDiagonalPairIndex_injective hdiag h)
    | inr b => exact False.elim ((prefixOrdinary_ne_diagonal hfit hdiag b a) h.symm)
  | inr a =>
    cases b with
    | inl b => exact False.elim ((prefixOrdinary_ne_diagonal hfit hdiag a b) h)
    | inr b => exact congrArg Sum.inr (prefixOrdinaryPairIndex_injective hfit h)

/-- Actual physical pair-incidence weight on one labelled row. -/
noncomputable def prefixStageRowIncidence {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n) : PrefixStagePair d layers n → ℝ
  | Sum.inl (rect, pair) =>
      rectanglePairWeight hs choice (fun c => c.1 = r) (prefixRectanglePairSlot hrect ((j, rect), pair))
  | Sum.inr (network, layer, edge) =>
      if network = 0 then
        LayerPacking.layerRowWeight (prefixStageLayer rows hrows j layer).1
          (prefixStageLayer rows hrows j layer).2 r edge
      else
        LayerPacking.layerColumnWeight (prefixStageLayer cols hcols j layer).1
          (prefixStageLayer cols hcols j layer).2 r edge

/-- Actual physical pair-incidence weight on one labelled column. -/
noncomputable def prefixStageColumnIncidence {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n) : PrefixStagePair d layers n → ℝ
  | Sum.inl (rect, pair) =>
      rectanglePairWeight hs choice (fun x => x.2 = c) (prefixRectanglePairSlot hrect ((j, rect), pair))
  | Sum.inr (network, layer, edge) =>
      if network = 0 then
        LayerPacking.layerColumnWeight (prefixStageLayer rows hrows j layer).1
          (prefixStageLayer rows hrows j layer).2 c edge
      else
        LayerPacking.layerRowWeight (prefixStageLayer cols hcols j layer).1
          (prefixStageLayer cols hcols j layer).2 c edge

/-- The row labels reproduce exactly the previously verified rectangle and
ordinary physical squared-weight invoices. -/
theorem prefixStageRowIncidence_sq_sum {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n) :
    (∑ x, (prefixStageRowIncidence hrect hs choice rows cols hrows hcols j r x) ^ 2) =
      prefixRectangleStageInvoice hrect hs choice (fun c => c.1 = r) j +
        physicalRowStageInvoice rows cols hrows hcols j r := by
  simp [prefixStageRowIncidence, prefixRectangleStageInvoice, physicalRowStageInvoice,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

/-- The column labels reproduce the corresponding physical invoices. -/
theorem prefixStageColumnIncidence_sq_sum {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n) :
    (∑ x, (prefixStageColumnIncidence hrect hs choice rows cols hrows hcols j c x) ^ 2) =
      prefixRectangleStageInvoice hrect hs choice (fun x => x.2 = c) j +
        physicalColumnStageInvoice rows cols hrows hcols j c := by
  simp [prefixStageColumnIncidence, prefixRectangleStageInvoice, physicalColumnStageInvoice,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]

end
end Sude
