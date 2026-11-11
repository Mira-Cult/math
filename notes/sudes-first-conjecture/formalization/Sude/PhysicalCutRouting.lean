import Sude.SimpleResidualPath

/-! Compose proved integral routing with the actual two-network swaps. -/
namespace Sude
noncomputable section

/-- With installed complete reservoirs, every pair of zero-total integer
demands satisfying the respective cut inequalities is realized in the
actual square by swaps, from one fixed reference. -/
theorem twoNetworks_realize_cut_demands {n : ℕ} {Er Ec : Type*}
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
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ dr dc : Fin n → ℤ,
      (∑ r, dr r = 0) → (∑ c, dc c = 0) →
      (∀ S : Finset (Fin n), |∑ r ∈ S, dr r| ≤
        ((((N / 2) * (cutEdges BR.source BR.target S).card) : ℕ) : ℤ)) →
      (∀ S : Finset (Fin n), |∑ c ∈ S, dc c| ≤
        ((((N / 2) * (cutEdges BC.source BC.target S).card) : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = 2 * dr r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = 2 * dc c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨b₀, hm, ha, hfixed, hrealize⟩ :=
    twoNetworks_realize_bounded_integer_flows a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC N hR hC
  refine ⟨b₀, hm, ha, hfixed, ?_⟩
  intro dr dc hzr hzc hcutr hcutc
  obtain ⟨fr, hfr, hdivr⟩ := integer_flow_of_cut_inequalities BR.source BR.target dr (N / 2) hzr hcutr
  obtain ⟨fc, hfc, hdivc⟩ := integer_flow_of_cut_inequalities BC.source BC.target dc (N / 2) hzc hcutc
  obtain ⟨b, hrows, hcols, hm, ha, hfixed, hpool, hinj⟩ :=
    hrealize fr (fun e => abs_le.mp (hfr e)) fc (fun e => abs_le.mp (hfc e))
  refine ⟨b, ?_, ?_, hm, ha, hfixed, hpool, hinj⟩
  · intro r
    simpa [hdivr r] using hrows r
  · intro c
    simpa [hdivc c] using hcols c


/-- FC2K's stated expansion and integer demand box route both networks
through actual square permutations, without assuming a flow. -/
theorem twoNetworks_realize_fc2k_demands {n : ℕ} {Er Ec : Type*}
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
    (N B : ℕ) (hR : ∀ e, 2 * N ≤ BR.radius e) (hC : ∀ e, 2 * N ≤ BC.radius e)
    (hN : 2000 ≤ N) (hB : 400000 * B < 199 * 999 * N)
    (hexpr : ∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
      200 * (cutEdges BR.source BR.target S).card)
    (hexpc : ∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
      200 * (cutEdges BC.source BC.target S).card) :
    ∃ b₀ : Cell n ≃ Fin (n * n),
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ dr dc : Fin n → ℤ,
      (∑ r, dr r = 0) → (∑ c, dc c = 0) →
      (∀ r, |dr r| ≤ (B : ℤ)) → (∀ c, |dc c| ≤ (B : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = 2 * dr r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = 2 * dc c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨b₀, hm, ha, hfixed, hrealize⟩ :=
    twoNetworks_realize_cut_demands a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC N hR hC
  refine ⟨b₀, hm, ha, hfixed, ?_⟩
  intro dr dc hzr hzc hbr hbc
  exact hrealize dr dc hzr hzc
    (fc2k_cut_inequalities BR.source BR.target dr N B hN hB hzr hbr hexpr)
    (fc2k_cut_inequalities BC.source BC.target dc N B hN hB hzc hbc hexpc)


end
end Sude
