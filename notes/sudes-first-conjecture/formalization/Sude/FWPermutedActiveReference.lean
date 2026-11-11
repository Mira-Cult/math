import Sude.FWPermutedCenteredNetworks
import Sude.ActiveSupportCenteredInvoice
import Sude.FlowRealization

/-! A fresh active-support-preserving reference for supplied centered
networks. No relation to another reference or line bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- Construct a fresh reference for the supplied same-square networks and
realize all supplied bounded integer flows, retaining outside-active values,
the active value image, and the exact invoice. -/
theorem fw_permuted_centered_active_reference {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (a : Cell n ≃ Fin (n*n)) (reserved active : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (hrowActive : LayerPacking.layersSupport rows ⊆ active)
    (hcolActive : LayerPacking.transposeCells (LayerPacking.layersSupport cols) ⊆ active)
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
      (∀ c ∉ active, entry b₀ c = entry a c) ∧
      active.image (entry b₀) = active.image (entry a) ∧
      Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
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
        (∀ c ∉ active, entry b c = entry a c) ∧
        active.image (entry b) = active.image (entry a) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  dsimp only
  have hRs : BR.source = fun e : Fin 3 × Fin n => e.2 := funext fun e => (hends e).1
  have hCs : BC.source = fun e : Fin 3 × Fin n => e.2 := funext fun e => (hends e).2.1
  have hRt : BR.target = fun e : Fin 3 × Fin n => p e.1 e.2 := funext fun e => (hends e).2.2.1
  have hCt : BC.target = fun e : Fin 3 × Fin n => p e.1 e.2 := funext fun e => (hends e).2.2.2
  have hR : ∀ e, 2 * ((n / 450) * poolMaximum n) ≤ BR.radius e := fun e => (hcapacity e).2.2
  have hC : ∀ e, 2 * ((n / 450) * poolMaximum n) ≤ BC.radius e := by
    intro e
    rw [(hcapacity e).2.1, ← (hcapacity e).1]
    exact hR e
  obtain ⟨b₀, hinvoice, hm, ha, hfixed, houtside, himage, hpool, hinj, hflows⟩ :=
    twoNetworks_centered_invoice_preserves_active_values a reserved active rows cols hr hc
      hrowActive hcolActive rowGap colGap hrowGap hcolGap BR BC
  refine ⟨b₀, hinvoice, hm, ha, hfixed, houtside, himage, hpool, hinj, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨hre, hrl, hrh⟩ := scaled_flow_within_center BR.radius ((n / 450) * poolMaximum n) fr hR hfr
  obtain ⟨hce, hcl, hch⟩ := scaled_flow_within_center BC.radius ((n / 450) * poolMaximum n) fc hC hfc
  obtain ⟨b, hrows, hcols, hm', ha', hfixed', houtside', himage', hpool', hinj'⟩ :=
    hflows (fun e => 2 * fr e) hre hrl hrh (fun e => 2 * fc e) hce hcl hch
  refine ⟨b, ?_, ?_, hm', ha', hfixed', houtside', himage', hpool', hinj'⟩
  · intro r
    exact (hrows r).trans (edgeTransfer_sum_scale_two BR.source BR.target fr r) |>.trans (by rw [hRs, hRt])
  · intro c
    exact (hcols c).trans (edgeTransfer_sum_scale_two BC.source BC.target fc c) |>.trans (by rw [hCs, hCt])

end
end Sude
