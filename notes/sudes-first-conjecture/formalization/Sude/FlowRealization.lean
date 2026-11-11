import Sude.FamilyGrid

/-! Physical realization of supplied bounded integral edge flows. The
existence of an integral flow from cut inequalities is not assumed or proved. -/
namespace Sude
noncomputable section

/-- Source capacity gate for g=2: ordinary coverage at least 2N contains
every transfer of size at most 2*floor(N/2) around the fixed center. -/
theorem evenGridCenter_pays_capacity (R N : ℕ) (hR : 2 * N ≤ R) :
    2 * (N / 2) ≤ evenGridCenter R := by
  dsimp [evenGridCenter]
  omega

theorem scaled_flow_within_center {E : Type*} (R : E → ℕ) (N : ℕ)
    (flow : E → ℤ) (hcoverage : ∀ e, 2 * N ≤ R e)
    (hflow : ∀ e, -((N / 2 : ℕ) : ℤ) ≤ flow e ∧ flow e ≤ ((N / 2 : ℕ) : ℤ)) :
    (∀ e, (2 : ℤ) ∣ 2 * flow e) ∧
    (∀ e, -(evenGridCenter (R e) : ℤ) ≤ 2 * flow e) ∧
    (∀ e, 2 * flow e ≤ evenGridCenter (R e)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e; exact ⟨flow e, rfl⟩
  · intro e
    have hc := evenGridCenter_pays_capacity (R e) N (hcoverage e)
    have hf := (hflow e).1
    omega
  · intro e
    have hc := evenGridCenter_pays_capacity (R e) N (hcoverage e)
    have hf := (hflow e).2
    omega

/-- Scaling an integer flow by two scales its signed vertex transfer by two. -/
theorem edgeTransfer_scale_two {E : Type*} {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (e : E) (r : Fin n) :
    edgeTransfer source target (fun x => 2 * flow x) e r =
      2 * edgeTransfer source target flow e r := by
  unfold edgeTransfer
  split_ifs <;> ring

theorem edgeTransfer_sum_scale_two {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (r : Fin n) :
    (∑ e : E, edgeTransfer source target (fun x => 2 * flow x) e r) =
      2 * ∑ e : E, edgeTransfer source target flow e r := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact edgeTransfer_scale_two source target flow e r

/-- Exact FC2K rounding gate. Here N=K*X and B bounds the magnitude of
an integer demand after division by g=2. The displayed strict demand bound
is precisely `(999/1000)*(199/200)*N` before the division by two. -/
theorem fc2k_floor_capacity_gate (N B : ℕ) (hN : 2000 ≤ N)
    (hB : 400000 * B < 199 * 999 * N) :
    200 * B < 199 * (N / 2) := by
  omega

/-- A fixed joint reference realizes any subsequently supplied bounded
integer flows on the two physical networks, with capacity floor(N/2).
All physical line effects are twice the directed integral divergence. -/
theorem twoNetworks_realize_bounded_integer_flows {n : ℕ} {Er Ec : Type*}
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
  obtain ⟨Sr₀, Sc₀, b₀, _, _, _, _, hbaseMain, hbaseAnti, hbaseFixed, hrealize⟩ :=
    twoNetworks_centered_transfers a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC
  refine ⟨b₀, hbaseMain, hbaseAnti, hbaseFixed, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨hre, hrl, hrh⟩ := scaled_flow_within_center BR.radius N fr hR hfr
  obtain ⟨hce, hcl, hch⟩ := scaled_flow_within_center BC.radius N fc hC hfc
  obtain ⟨b, hrows, hcols, hm, ha, hfixed, hpool, hinj⟩ :=
    hrealize (fun e => 2 * fr e) hre hrl hrh (fun e => 2 * fc e) hce hcl hch
  refine ⟨b, ?_, ?_, hm, ha, hfixed, hpool, hinj⟩
  · intro r
    exact (hrows r).trans (edgeTransfer_sum_scale_two BR.source BR.target fr r)
  · intro c
    exact (hcols c).trans (edgeTransfer_sum_scale_two BC.source BC.target fc c)

/-- If bounded integral flows with the displayed divergences are supplied for
prime targets, the physical reference leads to a public square. The reference
is chosen before the targets and flows; neither flow existence nor prime
diagonals are assumed by the preceding realization theorem. -/
theorem twoNetworks_square_from_integral_flows {n : ℕ} {Er Ec : Type*}
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
      ∀ fr : Er → ℤ, (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Ec → ℤ, (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ rowTarget colTarget : Fin n → ℕ,
      (∀ r, 2 * ∑ e : Er, edgeTransfer BR.source BR.target fr e r =
        (rowTarget r : ℤ) - rowSum b₀ r) →
      (∀ c, 2 * ∑ e : Ec, edgeTransfer BC.source BC.target fc e c =
        (colTarget c : ℤ) - columnSum b₀ c) →
      (∀ r, Nat.Prime (rowTarget r)) → (∀ c, Nat.Prime (colTarget c)) →
      Nat.Prime (mainSum a) → Nat.Prime (antiSum a) → HasSquare n := by
  obtain ⟨b₀, hbaseMain, hbaseAnti, hbaseFixed, hrealize⟩ :=
    twoNetworks_realize_bounded_integer_flows a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC N hR hC
  refine ⟨b₀, hbaseMain, hbaseAnti, hbaseFixed, ?_⟩
  intro fr hfr fc hfc rowTarget colTarget hrd hcd hrp hcp hmp hap
  obtain ⟨b, hrows, hcols, hm, ha, _, _, _⟩ := hrealize fr hfr fc hfc
  have hrowEq : ∀ r, rowSum b r = rowTarget r := by
    intro r
    have hh := hrows r
    rw [hrd r] at hh
    exact_mod_cast (show (rowSum b r : ℤ) = (rowTarget r : ℤ) by omega)
  have hcolEq : ∀ c, columnSum b c = colTarget c := by
    intro c
    have hh := hcols c
    rw [hcd c] at hh
    exact_mod_cast (show (columnSum b c : ℤ) = (colTarget c : ℤ) by omega)
  refine ⟨b, ?_⟩
  exact ⟨fun r => (hrowEq r).symm ▸ hrp r,
    fun c => (hcolEq c).symm ▸ hcp c,
    hm.symm ▸ (hbaseMain.symm ▸ hmp), ha.symm ▸ (hbaseAnti.symm ▸ hap)⟩

end
end Sude
