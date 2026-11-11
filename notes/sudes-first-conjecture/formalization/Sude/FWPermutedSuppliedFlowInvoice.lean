import Sude.FWPermutedCenteredNetworks
import Sude.FWCenteredFlowInvoice

/-! Supplied-flow realization for the centered networks exported by the
permuted physical construction. Flow existence and targets are not asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Pointwise graph and radius facts in `fw_permuted_centered_networks`
suffice for the same-square supplied-flow realization with its exact center
invoice. Signed integer edge flows are bounded by floor(N/2); physical line
changes equal twice their graph divergence. -/
theorem fw_permuted_centered_supplied_flows_with_invoice {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (a : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ) (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap))
    (hends : ∀ edge, BR.source edge = edge.2 ∧ BC.source edge = edge.2 ∧
      BR.target edge = p edge.1 edge.2 ∧ BC.target edge = p edge.1 edge.2)
    (R : Fin 3 × Fin n → ℕ)
    (hcapacity : ∀ edge, BR.radius edge = R edge ∧ BC.radius edge = R edge ∧
      2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge) :
    let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    ∃ b₀ : Cell n ≃ Fin (n*n),
      TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  have hRs : BR.source = fun e : Fin 3 × Fin n => e.2 := funext fun e => (hends e).1
  have hCs : BC.source = fun e : Fin 3 × Fin n => e.2 := funext fun e => (hends e).2.1
  have hRt : BR.target = fun e : Fin 3 × Fin n => p e.1 e.2 := funext fun e => (hends e).2.2.1
  have hCt : BC.target = fun e : Fin 3 × Fin n => p e.1 e.2 := funext fun e => (hends e).2.2.2
  have hR : ∀ edge, 2 * ((n / 450) * poolMaximum n) ≤ BR.radius edge := fun e => (hcapacity e).2.2
  have hC : ∀ edge, 2 * ((n / 450) * poolMaximum n) ≤ BC.radius edge := by
    intro e
    rw [(hcapacity e).2.1, ← (hcapacity e).1]
    exact hR e
  exact fw_centered_networks_realize_supplied_flows_with_invoice p a reserved rows cols hr hc rowGap colGap
    hrowGap hcolGap BR BC hRs hRt hCs hCt hR hC

end
end Sude
