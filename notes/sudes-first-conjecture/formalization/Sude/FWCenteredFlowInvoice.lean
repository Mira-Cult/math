import Sude.FWCenteredSuppliedFlows

/-! Retain the physical center invoice for the same reference that realizes
subsequent bounded flows. No quantitative line or target bound is asserted. -/
namespace Sude
noncomputable section

/-- Selected center subsets and their exact signed effects on the supplied
reference, for both physical networks. -/
def TwoNetworkReferenceInvoice {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a b₀ : Cell n ≃ Fin (n * n)) (rows cols : List (LayerPacking.Layer n))
    {reserved : Finset (Cell n)}
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ) (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap)) : Prop :=
  ∃ (Sr₀ : Finset (Fin rows.length × Fin n)) (Sc₀ : Finset (Fin cols.length × Fin n)),
    Sr₀ ⊆ Finset.univ.biUnion BR.block ∧ Sc₀ ⊆ Finset.univ.biUnion BC.block ∧
    (∀ e, ((∑ k ∈ Sr₀ ∩ BR.block e, rowGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BR.radius e)) ∧
    (∀ e, ((∑ k ∈ Sc₀ ∩ BC.block e, colGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BC.radius e)) ∧
    (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) = ∑ k ∈ Sr₀, layerTransfer rows rowGap k r) ∧
    (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc₀, layerTransfer cols colGap k c) ∧
    (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
      ∑ e : Er, edgeTransfer BR.source BR.target (fun e => evenGridCenter (BR.radius e)) e r) ∧
    (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
      ∑ e : Ec, edgeTransfer BC.source BC.target (fun e => evenGridCenter (BC.radius e)) e c)

/-- Retain the exact reference invoice when scaling supplied integer flows. -/
theorem twoNetworks_realize_bounded_integer_flows_with_invoice {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap))
    (N : ℕ) (hR : ∀ e, 2 * N ≤ BR.radius e) (hC : ∀ e, 2 * N ≤ BC.radius e) :
    ∃ b₀ : Cell n ≃ Fin (n * n),
      TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ fr : Er → ℤ, (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Ec → ℤ, (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Er, edgeTransfer BR.source BR.target fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Ec, edgeTransfer BC.source BC.target fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨Sr₀, Sc₀, b₀, hr₀, hc₀, hrcenters, hccenters, hrows₀, hcols₀,
    hrinvoice, hcinvoice, hmain, hanti, hfixed, hrealize⟩ :=
    twoNetworks_centered_transfers_with_invoice a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC
  refine ⟨b₀, ⟨Sr₀, Sc₀, hr₀, hc₀, hrcenters, hccenters, hrows₀, hcols₀,
    hrinvoice, hcinvoice⟩, hmain, hanti, hfixed, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨hre, hrl, hrh⟩ := scaled_flow_within_center BR.radius N fr hR hfr
  obtain ⟨hce, hcl, hch⟩ := scaled_flow_within_center BC.radius N fc hC hfc
  obtain ⟨b, hrows, hcols, hm, ha, hfixed', hpool, hinj⟩ :=
    hrealize (fun e => 2 * fr e) hre hrl hrh (fun e => 2 * fc e) hce hcl hch
  refine ⟨b, ?_, ?_, hm, ha, hfixed', hpool, hinj⟩
  · intro r
    exact (hrows r).trans (edgeTransfer_sum_scale_two BR.source BR.target fr r)
  · intro c
    exact (hcols c).trans (edgeTransfer_sum_scale_two BC.source BC.target fc c)

/-- The FW endpoint specialization retains the identical reference invoice. -/
theorem fw_centered_networks_realize_supplied_flows_with_invoice {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap))
    (hRs : BR.source = fun e : Fin 3 × Fin n => e.2)
    (hRt : BR.target = fun e : Fin 3 × Fin n => p e.1 e.2)
    (hCs : BC.source = fun e : Fin 3 × Fin n => e.2)
    (hCt : BC.target = fun e : Fin 3 × Fin n => p e.1 e.2)
    (hR : ∀ e, 2 * ((n / 450) * poolMaximum n) ≤ BR.radius e)
    (hC : ∀ e, 2 * ((n / 450) * poolMaximum n) ≤ BC.radius e) :
    let N := (n / 450) * poolMaximum n
    let source : Fin 3 × Fin n → Fin n := fun e => e.2
    let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
    ∃ b₀ : Cell n ≃ Fin (n * n),
      TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer source target fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  dsimp only
  obtain ⟨b₀, hinvoice, hm, ha, hfixed, hflows⟩ :=
    twoNetworks_realize_bounded_integer_flows_with_invoice a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC ((n / 450) * poolMaximum n) hR hC
  refine ⟨b₀, hinvoice, hm, ha, hfixed, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨b, hrows, hcols, hm', ha', hfixed', hpool, hinj⟩ := hflows fr hfr fc hfc
  refine ⟨b, ?_, ?_, hm', ha', hfixed', hpool, hinj⟩
  · intro r
    simpa only [hRs, hRt] using hrows r
  · intro c
    simpa only [hCs, hCt] using hcols c

end
end Sude
