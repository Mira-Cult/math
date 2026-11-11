import Sude.PhysicalCutRouting
import Sude.FTTTargetList
import Mathlib.Algebra.BigOperators.Ring.Nat

/-! Exact parity and conservation interfaces for the finite target list. -/
namespace Sude
noncomputable section

/-- Every prescribed entry is an odd prime, since the enumeration omits 2. -/
theorem oddPrime_odd (i : ℕ) : Odd (oddPrime i) := by
  have hp : Nat.Prime (oddPrime i) := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i + 1)
  have hlt : 2 < oddPrime i := by
    have h := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) (show 0 < i + 1 by omega)
    simpa [oddPrime, Nat.nth_prime_zero_eq_two] using h
  exact hp.odd_of_ne_two (by omega)

/-- An odd number of odd entries has an odd sum, with labelled indices. -/
theorem odd_sum_of_odd_entries {n : ℕ} (hn : Odd n) (f : Fin n → ℕ)
    (hf : ∀ i, Odd (f i)) : Odd (∑ i, f i) := by
  rw [Finset.odd_sum_iff_odd_card_odd]
  simpa [hf, Fintype.card_fin] using hn

theorem rowSum_odd {n : ℕ} (hn : Odd n) (a : Cell n ≃ Fin (n * n)) (r : Fin n) :
    Odd (rowSum a r) := by
  apply odd_sum_of_odd_entries hn
  intro i
  exact oddPrime_odd _

theorem columnSum_odd {n : ℕ} (hn : Odd n) (a : Cell n ≃ Fin (n * n)) (c : Fin n) :
    Odd (columnSum a c) := by
  apply odd_sum_of_odd_entries hn
  intro i
  exact oddPrime_odd _

/-- Half of the signed target difference. It is exact when the two line
values have the same parity, and remains a total integer function. -/
def halfLineDemand (target baseline : ℕ) : ℤ := ((target : ℤ) - baseline) / 2

theorem halfLineDemand_exact (target baseline : ℕ)
    (ht : Odd target) (hb : Odd baseline) :
    2 * halfLineDemand target baseline = (target : ℤ) - baseline := by
  obtain ⟨x, hx⟩ := ht
  obtain ⟨y, hy⟩ := hb
  simp only [halfLineDemand]
  omega

/-- Compatibility of the full target total implies exact conservation of
all halved integer demands. No per-line distinctness is required. -/
theorem halfLineDemand_system {n : ℕ} (target baseline : Fin n → ℕ)
    (ht : ∀ i, Odd (target i)) (hb : ∀ i, Odd (baseline i))
    (hsum : ∑ i, target i = ∑ i, baseline i) :
    (∑ i, halfLineDemand (target i) (baseline i) = 0) ∧
    (∀ i, 2 * halfLineDemand (target i) (baseline i) =
      (target i : ℤ) - baseline i) := by
  have hpoint : ∀ i, 2 * halfLineDemand (target i) (baseline i) =
      (target i : ℤ) - baseline i := fun i => halfLineDemand_exact _ _ (ht i) (hb i)
  have hsumZ : (∑ i, (target i : ℤ)) = ∑ i, (baseline i : ℤ) := by exact_mod_cast hsum
  have hmul : 2 * (∑ i, halfLineDemand (target i) (baseline i)) = 0 := by
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, hsumZ, sub_self]
  exact ⟨by omega, hpoint⟩

/-- A full signed correction in the interval [-2B,2B] gives a bounded
integer half-demand. -/
theorem halfLineDemand_bound (target baseline B : ℕ)
    (ht : Odd target) (hb : Odd baseline)
    (hbound : |(target : ℤ) - baseline| ≤ (2 : ℤ) * B) :
    |halfLineDemand target baseline| ≤ (B : ℤ) := by
  have heq := halfLineDemand_exact target baseline ht hb
  obtain ⟨hl, hr⟩ := abs_le.mp hbound
  rw [abs_le]
  omega


/-- The FTT target vector supplies prime, odd, compatible line targets.
Given explicit physical reservoirs, graph expansion, a verified exact pool
total, prime starting diagonals, and the stated per-line baseline bounds,
the constructed square reaches all of those targets. No flow is assumed. -/
theorem fc2k_square_of_ftt_targets (r : Lucas.TargetRow) (h : Lucas.TargetRowValid r)
    {Er Ec : Type*} [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell r.order ≃ Fin (r.order * r.order)) (reserved : Finset (Cell r.order))
    (rows cols : List (LayerPacking.Layer r.order))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin r.order → ℕ)
    (colGap : Fin cols.length → Fin r.order → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin r.order) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin r.order) (hc.columnPairs a colGap hcolGap))
    (N B : ℕ) (hR : ∀ e, 2 * N ≤ BR.radius e) (hC : ∀ e, 2 * N ≤ BC.radius e)
    (hN : 2000 ≤ N) (hB : 400000 * B < 199 * 999 * N)
    (hexpr : ∀ S : Finset (Fin r.order), 199 * min S.card (r.order - S.card) ≤
      200 * (cutEdges BR.source BR.target S).card)
    (hexpc : ∀ S : Finset (Fin r.order), 199 * min S.card (r.order - S.card) ≤
      200 * (cutEdges BC.source BC.target S).card)
    (hpool : r.total = Lucas.poolTotal r.order) :
    ∃ b₀ : Cell r.order ≃ Fin (r.order * r.order),
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ((∀ i, |(Lucas.targetAt r h i : ℤ) - rowSum b₀ i| ≤ (2 : ℤ) * B) →
       (∀ i, |(Lucas.targetAt r h i : ℤ) - columnSum b₀ i| ≤ (2 : ℤ) * B) →
       Nat.Prime (mainSum a) → Nat.Prime (antiSum a) → HasSquare r.order) := by
  have hn : Odd r.order := Nat.odd_iff.mpr h.2.2.2.2.1
  have htarget : ∀ i, Odd (Lucas.targetAt r h i) :=
    fun i => Nat.odd_iff.mpr (Lucas.targetAt_odd r h i)
  obtain ⟨b₀, hm, ha, hfixed, hrealize⟩ :=
    twoNetworks_realize_fc2k_demands a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap BR BC N B hR hC hN hB hexpr hexpc
  refine ⟨b₀, hm, ha, hfixed, ?_⟩
  intro hbr hbc hmp hap
  have ⟨hrowsTotal, hcolsTotal⟩ := Lucas.targetAt_axis_compatibility r h b₀ hpool
  let dr : Fin r.order → ℤ := fun i => halfLineDemand (Lucas.targetAt r h i) (rowSum b₀ i)
  let dc : Fin r.order → ℤ := fun i => halfLineDemand (Lucas.targetAt r h i) (columnSum b₀ i)
  have ⟨hzr, her⟩ := halfLineDemand_system (Lucas.targetAt r h) (rowSum b₀)
    htarget (rowSum_odd hn b₀) hrowsTotal
  have ⟨hzc, hec⟩ := halfLineDemand_system (Lucas.targetAt r h) (columnSum b₀)
    htarget (columnSum_odd hn b₀) hcolsTotal
  have hdr : ∀ i, |dr i| ≤ (B : ℤ) := fun i =>
    halfLineDemand_bound _ _ B (htarget i) (rowSum_odd hn b₀ i) (hbr i)
  have hdc : ∀ i, |dc i| ≤ (B : ℤ) := fun i =>
    halfLineDemand_bound _ _ B (htarget i) (columnSum_odd hn b₀ i) (hbc i)
  obtain ⟨b, hrow, hcol, hmain, hanti, _, _, _⟩ := hrealize dr dc hzr hzc hdr hdc
  have hrowEq : ∀ i, rowSum b i = Lucas.targetAt r h i := by
    intro i
    have h₁ := hrow i
    have h₂ := her i
    change (rowSum b i : ℤ) - rowSum b₀ i =
      2 * halfLineDemand (Lucas.targetAt r h i) (rowSum b₀ i) at h₁
    exact_mod_cast (show (rowSum b i : ℤ) = Lucas.targetAt r h i by omega)
  have hcolEq : ∀ i, columnSum b i = Lucas.targetAt r h i := by
    intro i
    have h₁ := hcol i
    have h₂ := hec i
    change (columnSum b i : ℤ) - columnSum b₀ i =
      2 * halfLineDemand (Lucas.targetAt r h i) (columnSum b₀ i) at h₁
    exact_mod_cast (show (columnSum b i : ℤ) = Lucas.targetAt r h i by omega)
  refine ⟨b, ?_⟩
  exact ⟨fun i => (hrowEq i).symm ▸ Lucas.targetAt_prime r h i,
    fun i => (hcolEq i).symm ▸ Lucas.targetAt_prime r h i,
    hmain.symm ▸ (hm.symm ▸ hmp), hanti.symm ▸ (ha.symm ▸ hap)⟩


end
end Sude
