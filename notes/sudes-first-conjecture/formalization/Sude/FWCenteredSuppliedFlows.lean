import Sude.FlowRealization

/-! Realize supplied bounded flows on two already constructed FW centered
networks, without asserting the existence of flows for target demands. -/
namespace Sude
noncomputable section

/-- The same supplied square and centered networks admit one joint reference
from which every supplied pair of bounded integral graph flows is physically
realized. Their line effects are twice the signed graph divergence. -/
theorem fw_centered_networks_realize_supplied_flows {n : ℕ}
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
  obtain ⟨b₀, hm, ha, hfixed, hflows⟩ :=
    twoNetworks_realize_bounded_integer_flows a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC ((n / 450) * poolMaximum n) hR hC
  refine ⟨b₀, hm, ha, hfixed, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨b, hrows, hcols, hm', ha', hfixed', hpool, hinj⟩ := hflows fr hfr fc hfc
  refine ⟨b, ?_, ?_, hm', ha', hfixed', hpool, hinj⟩
  · intro r
    simpa only [hRs, hRt] using hrows r
  · intro c
    simpa only [hCs, hCt] using hcols c

end
end Sude
