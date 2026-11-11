import Sude.T75FineGridBinning
import Sude.T75UnitBracketTargets
import Sude.T75TwoClassMidpointMargin
import Sude.T75UniformSeedGrid
import Sude.ReservedPoolMean

/-!
# Compact and General-Parameter T75 Fine-Grid Binning

Provides two generalizations of `T75FineGridBinning.t75_seed_chain_package_from_supplies`
together with a band-independent target wrapper `t75_targets_from_seed_chain_general`:

1. `t75_compact_targets_from_supplies`: two-phase geometric step-gap chain (`C = 24`,
   2 copies per step, growth ratios `69 / 65` up to `D / 16` and `31 / 30` from `D / 16` to `D`),
   using at most `P ≤ 324 + 2 * k1` narrow pairs (`979 + 6 * k1 ≤ n`), reaching down to `n = 2001`.
2. `t75_general_targets_from_supplies`: arbitrary-density (`1 ≤ C`, `D < C * h * A.card`) and
   arbitrary-depth (`k : ℕ`, `D < 2 * C * h * 2 ^ k`) doubling chain using at most
   `P ≤ 4 * C * (k + 1) + 2` narrow pairs, covering `9301 ≤ n ≤ 19483` and the entire
   unbounded upper tail `n ≥ 35735`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Band-independent T75 prime target vector from a seed-extended step-gap chain. -/
theorem t75_targets_from_seed_chain_general {β : Type*} [DecidableEq β]
    {n m h : ℕ} (hn_pos : 0 < n) (hn : Odd n)
    (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (narrow wide : Finset β) (low gap : β → ℕ)
    (hdis : Disjoint narrow wide) (hcount : 2 * narrow.card + 5 ≤ wide.card)
    (hlen : m + (narrow ∪ wide).card = n)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD_nonneg : 0 ≤ D) (hyD_gt : (2 : ℝ) < y - D)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y - D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y + D)
    (hprime : ∀ i ∈ narrow ∪ wide, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hwindow : ∀ i ∈ narrow ∪ wide, y - D ≤ (low i : ℝ) ∧ ((low i + gap i : ℕ) : ℝ) ≤ y + D)
    (seed : Finset β) (labels : List β)
    (hS : seed ∪ labels.toFinset = narrow ∪ wide)
    (hseed : ∀ i ∈ seed, gap i = h)
    (hnodup : labels.Nodup) (hfresh : ∀ i ∈ labels, i ∉ seed)
    (hchain : StepGapChain gap h (∑ i ∈ seed, gap i) labels)
    (hnarrow : ∀ i ∈ narrow, |(low i : ℝ) + (gap i : ℝ) / 2 - y| ≤ D / 2)
    (hwide : ∀ i ∈ wide, |(low i : ℝ) + (gap i : ℝ) / 2 - y| ≤ D / 4)
    (hgap : ∀ i ∈ wide, D ≤ (gap i : ℝ)) :
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  have hpositive : 0 < h := by
    have hh' := hh
    simp only [t75FavorableGaps, Finset.mem_insert, Finset.mem_singleton] at hh'
    omega
  have hgrid := t75_uniform_seed_extend gap h seed labels hpositive hseed hnodup hfresh hchain
  rw [hS] at hgrid
  have hcenter : (Lucas.poolTotal n : ℝ) = (n : ℝ) * y := by
    rw [hy, prescribedPoolValues_mean]
    have h1 := t75_pool_mean_line_total hn_pos
    rw [t75_line_mean_eq_order_mul_pool_mean hn_pos] at h1
    nlinarith
  have hmargin := t75_two_class_hmargin narrow wide low gap y D hD_nonneg hdis hcount hnarrow hwide hgap
  obtain ⟨_xs, _lo, _hi, _values, _chosen, _hlen_xs, _hsub, _hforall, _ht, f, _hf_get, hf_sum, hf_valid⟩ :=
    t75_targets_from_unit_bracket_supply hn hm hh (narrow ∪ wide) low gap hlen y D hD_nonneg
      hsupply hprime hwindow hgrid hcenter hmargin hyD_gt
  exact ⟨f, hf_sum, hf_valid⟩

/-- Package helper converting any `(seed_count, chain_narrow)` reaching `2 * D` into the
    seed-chain data required by `t75_targets_from_seed_chain_general`. -/
private theorem package_seed_and_narrow_chain
    {n h b_w seed_count : ℕ} (hh_pos : 0 < h) (_hseed_pos : 0 < seed_count)
    (y D : ℝ)
    (r0 : ℕ) (hr0_prime : Nat.Prime r0) (hr0h_prime : Nat.Prime (r0 + h))
    (hr0_lo : y - D / 2 ≤ (r0 : ℝ)) (hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2)
    (A : Finset ℕ) (hA_prime : ∀ p ∈ A, Nat.Prime p)
    (hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2)
    (chain_narrow : List (ℕ × ℕ))
    (hPW_le : 3 * (seed_count + chain_narrow.length) + 7 ≤ n)
    (hmem_narrow : ∀ x ∈ chain_narrow, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2)
    (hchain_narrow : StepGapChain Prod.snd h (seed_count * h) chain_narrow)
    (hR_two_D : 2 * D ≤ ((seed_count * h + (chain_narrow.map Prod.snd).sum : ℕ) : ℝ))
    (uw vw : ℕ) (huw_prime : Nat.Prime uw) (hvw_prime : Nat.Prime vw)
    (huw_mod : uw % h = b_w) (hvw_mod : vw % h = b_w)
    (huw_int : y - D ≤ (uw : ℝ) ∧ (uw : ℝ) ≤ y - D / 2)
    (hvw_int : y + D / 2 ≤ (vw : ℝ) ∧ (vw : ℝ) ≤ y + D) :
    ∃ (m : ℕ) (narrow wide seed : Finset (ℕ × (ℕ × ℕ)))
      (low gap : ℕ × (ℕ × ℕ) → ℕ) (labels : List (ℕ × (ℕ × ℕ))),
      2 ≤ m ∧
      Disjoint narrow wide ∧
      2 * narrow.card + 5 ≤ wide.card ∧
      m + (narrow ∪ wide).card = n ∧
      (∀ z ∈ narrow ∪ wide, Nat.Prime (low z) ∧ Nat.Prime (low z + gap z)) ∧
      (∀ z ∈ narrow ∪ wide, y - D ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D) ∧
      seed ∪ labels.toFinset = narrow ∪ wide ∧
      (∀ z ∈ seed, gap z = h) ∧
      labels.Nodup ∧
      (∀ z ∈ labels, z ∉ seed) ∧
      StepGapChain gap h (∑ z ∈ seed, gap z) labels ∧
      (∀ z ∈ narrow, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 2) ∧
      (∀ z ∈ wide, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 4) ∧
      (∀ z ∈ wide, D ≤ (gap z : ℝ)) := by
  let dw : ℕ := vw - uw
  have huw_le_vw : uw ≤ vw := by
    have : (uw : ℝ) ≤ (vw : ℝ) := by linarith [huw_int.2, hvw_int.1]
    exact_mod_cast this
  have hdw_dvd : h ∣ dw := by
    have hudiv := (Nat.div_add_mod uw h).symm
    have hvdiv := (Nat.div_add_mod vw h).symm
    refine ⟨vw / h - uw / h, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega
  have hdw_lo : D ≤ (dw : ℝ) := by
    have hcast : (dw : ℝ) = (vw : ℝ) - (uw : ℝ) := Nat.cast_sub huw_le_vw
    linarith [huw_int.2, hvw_int.1]
  have hdw_hi : (dw : ℝ) ≤ 2 * D := by
    have hcast : (dw : ℝ) = (vw : ℝ) - (uw : ℝ) := Nat.cast_sub huw_le_vw
    linarith [huw_int.1, hvw_int.2]
  have hdw_le_R : dw ≤ seed_count * h + (chain_narrow.map Prod.snd).sum := by
    have : (dw : ℝ) ≤ ((seed_count * h + (chain_narrow.map Prod.snd).sum : ℕ) : ℝ) :=
      le_trans hdw_hi hR_two_D
    exact_mod_cast this
  let P : ℕ := seed_count + chain_narrow.length
  let W : ℕ := 2 * P + 5
  obtain ⟨seed_list, hseed_len, hseed_mem, _, _⟩ :=
    exists_replicate_chain h 0 seed_count (r0, h) (dvd_refl h) (by dsimp; omega)
  obtain ⟨wide_list, hwide_len, hwide_mem, _, hchain_wide⟩ :=
    exists_replicate_chain h (seed_count * h + (chain_narrow.map Prod.snd).sum) W (uw, dw)
      hdw_dvd (by dsimp; omega)
  let seed : Finset (ℕ × (ℕ × ℕ)) := (indexPairs 0 seed_list).toFinset
  let narrow : Finset (ℕ × (ℕ × ℕ)) := (indexPairs 0 (seed_list ++ chain_narrow)).toFinset
  let wide : Finset (ℕ × (ℕ × ℕ)) := (indexPairs P wide_list).toFinset
  let labels : List (ℕ × (ℕ × ℕ)) := indexPairs seed_count (chain_narrow ++ wide_list)
  let low : ℕ × (ℕ × ℕ) → ℕ := fun z => z.2.1
  let gap : ℕ × (ℕ × ℕ) → ℕ := fun z => z.2.2
  have hnarrow_card : narrow.card = P := by
    change (indexPairs 0 (seed_list ++ chain_narrow)).toFinset.card = P
    rw [indexPairs_toFinset_card, List.length_append, hseed_len]
  have hwide_card : wide.card = W := by
    change (indexPairs P wide_list).toFinset.card = W
    rw [indexPairs_toFinset_card, hwide_len]
  have hseed_card : seed.card = seed_count := by
    change (indexPairs 0 seed_list).toFinset.card = seed_count
    rw [indexPairs_toFinset_card, hseed_len]
  have hdis : Disjoint narrow wide := by
    rw [Finset.disjoint_left]
    intro z hzn hzw
    rw [List.mem_toFinset] at hzn hzw
    have h1 := (mem_indexPairs hzn).2.1
    have h2 := (mem_indexPairs hzw).1
    rw [List.length_append, hseed_len] at h1
    omega
  have hS : seed ∪ labels.toFinset = narrow ∪ wide := by
    change (indexPairs 0 seed_list).toFinset ∪ (indexPairs seed_count (chain_narrow ++ wide_list)).toFinset =
      (indexPairs 0 (seed_list ++ chain_narrow)).toFinset ∪ (indexPairs P wide_list).toFinset
    rw [indexPairs_toFinset_append 0 seed_list chain_narrow,
        indexPairs_toFinset_append seed_count chain_narrow wide_list]
    simp only [hseed_len, Nat.zero_add, Finset.union_assoc]
    rfl
  have hseed_gap : ∀ z ∈ seed, gap z = h := by
    intro z hz
    rw [List.mem_toFinset] at hz
    have hzeq := hseed_mem z.2 (mem_indexPairs hz).2.2
    simp [gap, hzeq]
  have hseed_sum : (∑ z ∈ seed, gap z) = seed_count * h := by
    calc
      (∑ z ∈ seed, gap z) = ∑ _z ∈ seed, h := Finset.sum_congr rfl hseed_gap
      _ = seed.card * h := by simp
      _ = seed_count * h := by rw [hseed_card]
  have hchain_combined : StepGapChain Prod.snd h (seed_count * h) (chain_narrow ++ wide_list) :=
    StepGapChain.append Prod.snd h (seed_count * h) chain_narrow wide_list hchain_narrow hchain_wide
  have hchain : StepGapChain gap h (∑ z ∈ seed, gap z) labels := by
    rw [hseed_sum]
    exact indexPairs_stepGapChain seed_count h (seed_count * h) (chain_narrow ++ wide_list) hchain_combined
  have hnodup : labels.Nodup := indexPairs_nodup seed_count (chain_narrow ++ wide_list)
  have hfresh : ∀ z ∈ labels, z ∉ seed := by
    intro z hzl hzs
    rw [List.mem_toFinset] at hzs
    have h1 := (mem_indexPairs hzl).1
    have h2 := (mem_indexPairs hzs).2.1
    rw [hseed_len] at h2
    omega
  have hunion_card : (narrow ∪ wide).card = P + W := by
    rw [Finset.card_union_of_disjoint hdis, hnarrow_card, hwide_card]
  have hPW_le' : P + W + 2 ≤ n := by
    dsimp [P, W]
    omega
  let m : ℕ := n - (P + W)
  have hm : 2 ≤ m := by omega
  have hlen : m + (narrow ∪ wide).card = n := by
    rw [hunion_card]
    omega
  have hcount : 2 * narrow.card + 5 ≤ wide.card := by
    rw [hnarrow_card, hwide_card]
  have hmem_narrow_pair : ∀ z ∈ narrow, z.2 = (r0, h) ∨ z.2 ∈ chain_narrow := by
    intro z hz
    rw [List.mem_toFinset] at hz
    rcases List.mem_append.mp (mem_indexPairs hz).2.2 with hm1 | hm2
    · exact Or.inl (hseed_mem z.2 hm1)
    · exact Or.inr hm2
  have hmem_wide_pair : ∀ z ∈ wide, z.2 = (uw, dw) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    exact hwide_mem z.2 (mem_indexPairs hz).2.2
  have hprime : ∀ z ∈ narrow ∪ wide, Nat.Prime (low z) ∧ Nat.Prime (low z + gap z) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzn | hzw
    · rcases hmem_narrow_pair z hzn with hseed_eq | hch
      · simp only [low, gap, hseed_eq]
        exact ⟨hr0_prime, hr0h_prime⟩
      · obtain ⟨hp1, hp2, _, _⟩ := hmem_narrow z.2 hch
        exact ⟨hA_prime _ hp1, hA_prime _ hp2⟩
    · have hw_eq := hmem_wide_pair z hzw
      simp only [low, gap, hw_eq]
      have : uw + dw = vw := by omega
      rw [this]
      exact ⟨huw_prime, hvw_prime⟩
  have hnarrow_bounds : ∀ z ∈ narrow, y - D / 2 ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D / 2 := by
    intro z hzn
    rcases hmem_narrow_pair z hzn with hseed_eq | hch
    · simp only [low, gap, hseed_eq]
      exact ⟨hr0_lo, hr0_hi⟩
    · obtain ⟨hp1, hp2, _, _⟩ := hmem_narrow z.2 hch
      exact ⟨(hA_int _ hp1).1, (hA_int _ hp2).2⟩
  have hwindow : ∀ z ∈ narrow ∪ wide, y - D ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzn | hzw
    · obtain ⟨hlo, hhi⟩ := hnarrow_bounds z hzn
      exact ⟨by linarith, by linarith [huw_int.1, hvw_int.1]⟩
    · have hw_eq := hmem_wide_pair z hzw
      simp only [low, gap, hw_eq]
      have hsum : uw + dw = vw := by omega
      rw [hsum]
      exact ⟨by linarith [huw_int.1, hvw_int.1], by linarith [huw_int.1, hvw_int.1, hvw_int.2]⟩
  have hnarrow_mid : ∀ z ∈ narrow, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 2 := by
    intro z hzn
    obtain ⟨hlo, hhi⟩ := hnarrow_bounds z hzn
    have hhi' : (low z : ℝ) + (gap z : ℝ) ≤ y + D / 2 := by exact_mod_cast hhi
    have hgap_nonneg : (0 : ℝ) ≤ (gap z : ℝ) := Nat.cast_nonneg _
    rw [abs_le]
    constructor <;> linarith
  have hwide_mid : ∀ z ∈ wide, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 4 := by
    intro z hzw
    have hw_eq := hmem_wide_pair z hzw
    simp only [low, gap, hw_eq]
    have hcast : (dw : ℝ) = (vw : ℝ) - (uw : ℝ) := Nat.cast_sub huw_le_vw
    rw [hcast, abs_le]
    constructor <;> linarith [huw_int.1, huw_int.2, hvw_int.1, hvw_int.2]
  have hgap_wide : ∀ z ∈ wide, D ≤ (gap z : ℝ) := by
    intro z hzw
    have hw_eq := hmem_wide_pair z hzw
    simp only [gap, hw_eq]
    exact hdw_lo
  exact ⟨m, narrow, wide, seed, low, gap, labels, hm, hdis, hcount, hlen, hprime, hwindow, hS,
    hseed_gap, hnodup, hfresh, hchain, hnarrow_mid, hwide_mid, hgap_wide⟩

/-! ### Part 1: Compact two-phase chain (`C = 24`, reaching `n = 2001`) -/

private theorem compact_phase1_step (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hR104 : 104 * h ≤ R) (hRD16 : (R : ℝ) ≤ D / 16)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 24 * (h : ℝ) * (A.card : ℝ)) :
    ∃ step_pairs : List (ℕ × ℕ),
      step_pairs.length = 2 ∧
      (∀ x ∈ step_pairs, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R step_pairs ∧
      69 * R < 65 * (R + (step_pairs.map Prod.snd).sum) := by
  have hRpos : 0 < R := by omega
  have hRposR : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hRpos
  have hDpos : (0 : ℝ) < D := by linarith
  have hhR : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  let q : ℕ := R / (26 * h)
  have hq4 : 4 ≤ q := by
    have h1 : 4 * (26 * h) ≤ R := by omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr h1
  have hcard : (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card := by
    have hdiv16 : (16 : ℝ) ≤ D / (R : ℝ) := by
      rw [le_div_iff₀ hRposR]
      linarith
    have hfl : ((⌊D / (R : ℝ)⌋₊ : ℕ) : ℝ) ≤ D / (R : ℝ) := Nat.floor_le (by positivity)
    have hK_le : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ (17 / 16 : ℝ) * (D / (R : ℝ)) := by
      push_cast
      linarith
    have hq_nat : q * (26 * h) ≤ R := Nat.div_mul_le_self R (26 * h)
    have hq_real : (q : ℝ) * (26 * (h : ℝ)) ≤ (R : ℝ) := by exact_mod_cast hq_nat
    have hm1 := mul_le_mul_of_nonneg_right hK_le (show (0 : ℝ) ≤ (q : ℝ) * (26 * (h : ℝ)) by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hq_real (show (0 : ℝ) ≤ (17 / 16 : ℝ) * (D / (R : ℝ)) by positivity)
    have hmul : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) * ((q : ℝ) * (26 * (h : ℝ))) ≤ (17 / 16 : ℝ) * D := by
      have hc : ((17 / 16 : ℝ) * (D / (R : ℝ))) * (R : ℝ) = (17 / 16 : ℝ) * D := by
        rw [mul_assoc, div_mul_cancel₀ _ hRposR.ne']
      linarith
    have hlt_real : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) < (A.card : ℝ) := by
      have hprod : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) * (26 * (h : ℝ)) <
          (A.card : ℝ) * (26 * (h : ℝ)) := by
        push_cast at hmul ⊢
        linarith
      exact lt_of_mul_lt_mul_right hprod (by positivity)
    exact_mod_cast hlt_real
  obtain ⟨p_min, p_max, hpmin, hpmax, hle, hdvd, hq_le, hgap_le⟩ :=
    pigeonhole_spatial_bin A u0 D R h b q hh hRpos (by omega) hA_int hA_mod hcard
  let d : ℕ := p_max - p_min
  have hd_pos : 0 < d := by
    have : 0 < q * h := Nat.mul_pos (by omega) hh
    omega
  refine ⟨List.replicate 2 (p_min, d), by simp, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    refine ⟨hpmin, ?_, hd_pos, hdvd⟩
    dsimp only
    have : p_min + d = p_max := by omega
    rw [this]
    exact hpmax
  · exact StepGapChain.replicate Prod.snd h R 2 (p_min, d) hdvd (by dsimp; omega)
  · rw [map_sum_replicate]
    dsimp only
    have hdiv_mod := (Nat.div_add_mod R (26 * h)).symm
    have hmod_lt : R % (26 * h) < 26 * h := Nat.mod_lt R (by omega)
    have hR_lt : R < 26 * h * (q + 1) := by
      change R < 26 * h * (R / (26 * h) + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h5q : 4 * (26 * h * (q + 1)) ≤ 130 * (q * h) := by
      have : 4 * (q + 1) ≤ 5 * q := by omega
      have hm := Nat.mul_le_mul_left (26 * h) this
      linarith
    have h130d : 130 * (q * h) ≤ 130 * d := Nat.mul_le_mul_left 130 hq_le
    omega

private theorem compact_phase1_loop (k : ℕ) (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hR104 : 104 * h ≤ R)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 24 * (h : ℝ) * (A.card : ℝ)) :
    ∃ chain : List (ℕ × ℕ),
      chain.length ≤ 2 * k ∧
      (∀ x ∈ chain, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R chain ∧
      (D / 16 < ((R + (chain.map Prod.snd).sum : ℕ) : ℝ) ∨
        R * 69 ^ k ≤ (R + (chain.map Prod.snd).sum) * 65 ^ k) := by
  induction k generalizing R with
  | zero =>
    refine ⟨[], by simp, by simp, StepGapChain.nil R, Or.inr (by simp)⟩
  | succ k ih =>
    by_cases hRD16 : (R : ℝ) ≤ D / 16
    · obtain ⟨step_pairs, hlen1, hmem1, hchain1, hgrow⟩ :=
        compact_phase1_step A u0 D R h b hh hR104 hRD16 hA_int hA_mod hA_card
      let R1 : ℕ := R + (step_pairs.map Prod.snd).sum
      obtain ⟨rest, hlen2, hmem2, hchain2, hor⟩ := ih R1 (by omega)
      refine ⟨step_pairs ++ rest, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hlen1]
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hmem1 x hx1
        · exact hmem2 x hx2
      · exact StepGapChain.append Prod.snd h R step_pairs rest hchain1 hchain2
      · rw [List.map_append, List.sum_append, ← Nat.add_assoc]
        rcases hor with hgt | hpow
        · exact Or.inl hgt
        · right
          have h1 : (R * 69) * 69 ^ k ≤ (R1 * 65) * 69 ^ k :=
            Nat.mul_le_mul_right (69 ^ k) (by omega)
          have h2 : (R1 * 69 ^ k) * 65 ≤ ((R1 + (rest.map Prod.snd).sum) * 65 ^ k) * 65 :=
            Nat.mul_le_mul_right 65 hpow
          calc
            R * 69 ^ (k + 1) = (R * 69) * 69 ^ k := by ring
            _ ≤ (R1 * 65) * 69 ^ k := h1
            _ = (R1 * 69 ^ k) * 65 := by ring
            _ ≤ ((R1 + (rest.map Prod.snd).sum) * 65 ^ k) * 65 := h2
            _ = (R1 + (rest.map Prod.snd).sum) * 65 ^ (k + 1) := by ring
    · exact ⟨[], by simp, by simp, StepGapChain.nil R, Or.inl (by simpa using lt_of_not_ge hRD16)⟩

private theorem compact_phase2_step (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hR192 : 192 * h ≤ R) (hRD : (R : ℝ) ≤ D)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 24 * (h : ℝ) * (A.card : ℝ)) :
    ∃ step_pairs : List (ℕ × ℕ),
      step_pairs.length = 2 ∧
      (∀ x ∈ step_pairs, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R step_pairs ∧
      31 * R < 30 * (R + (step_pairs.map Prod.snd).sum) := by
  have hRpos : 0 < R := by omega
  have hRposR : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hRpos
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le hRposR hRD
  have hhR : (0 : ℝ) < (h : ℝ) := Nat.cast_pos.mpr hh
  let q : ℕ := R / (48 * h)
  have hq4 : 4 ≤ q := by
    have h1 : 4 * (48 * h) ≤ R := by omega
    exact (Nat.le_div_iff_mul_le (by omega)).mpr h1
  have hcard : (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card := by
    have hdiv1 : (1 : ℝ) ≤ D / (R : ℝ) := (one_le_div hRposR).mpr hRD
    have hfl : ((⌊D / (R : ℝ)⌋₊ : ℕ) : ℝ) ≤ D / (R : ℝ) := Nat.floor_le (by positivity)
    have hK_le : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (D / (R : ℝ)) := by
      push_cast
      linarith
    have hq_nat : q * (48 * h) ≤ R := Nat.div_mul_le_self R (48 * h)
    have hq_real : (q : ℝ) * (48 * (h : ℝ)) ≤ (R : ℝ) := by exact_mod_cast hq_nat
    have hm1 := mul_le_mul_of_nonneg_right hK_le (show (0 : ℝ) ≤ (q : ℝ) * (48 * (h : ℝ)) by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hq_real (show (0 : ℝ) ≤ 2 * (D / (R : ℝ)) by positivity)
    have hmul : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) * ((q : ℝ) * (48 * (h : ℝ))) ≤ 2 * D := by
      have hc : (2 * (D / (R : ℝ))) * (R : ℝ) = 2 * D := by
        rw [mul_assoc, div_mul_cancel₀ _ hRposR.ne']
      linarith
    have hlt_real : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) < (A.card : ℝ) := by
      have hprod : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) * (48 * (h : ℝ)) <
          (A.card : ℝ) * (48 * (h : ℝ)) := by
        push_cast at hmul ⊢
        linarith
      exact lt_of_mul_lt_mul_right hprod (by positivity)
    exact_mod_cast hlt_real
  obtain ⟨p_min, p_max, hpmin, hpmax, hle, hdvd, hq_le, hgap_le⟩ :=
    pigeonhole_spatial_bin A u0 D R h b q hh hRpos (by omega) hA_int hA_mod hcard
  let d : ℕ := p_max - p_min
  have hd_pos : 0 < d := by
    have : 0 < q * h := Nat.mul_pos (by omega) hh
    omega
  refine ⟨List.replicate 2 (p_min, d), by simp, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    refine ⟨hpmin, ?_, hd_pos, hdvd⟩
    dsimp only
    have : p_min + d = p_max := by omega
    rw [this]
    exact hpmax
  · exact StepGapChain.replicate Prod.snd h R 2 (p_min, d) hdvd (by dsimp; omega)
  · rw [map_sum_replicate]
    dsimp only
    have hdiv_mod := (Nat.div_add_mod R (48 * h)).symm
    have hmod_lt : R % (48 * h) < 48 * h := Nat.mod_lt R (by omega)
    have hR_lt : R < 48 * h * (q + 1) := by
      change R < 48 * h * (R / (48 * h) + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h5q : 4 * (48 * h * (q + 1)) ≤ 240 * (q * h) := by
      have : 4 * (q + 1) ≤ 5 * q := by omega
      have hm := Nat.mul_le_mul_left (48 * h) this
      linarith
    have h240d : 240 * (q * h) ≤ 240 * d := Nat.mul_le_mul_left 240 hq_le
    omega

private theorem compact_phase2_loop (k : ℕ) (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hR192 : 192 * h ≤ R)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 24 * (h : ℝ) * (A.card : ℝ)) :
    ∃ chain : List (ℕ × ℕ),
      chain.length ≤ 2 * k ∧
      (∀ x ∈ chain, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R chain ∧
      (D < ((R + (chain.map Prod.snd).sum : ℕ) : ℝ) ∨
        R * 31 ^ k ≤ (R + (chain.map Prod.snd).sum) * 30 ^ k) := by
  induction k generalizing R with
  | zero =>
    refine ⟨[], by simp, by simp, StepGapChain.nil R, Or.inr (by simp)⟩
  | succ k ih =>
    by_cases hRD : (R : ℝ) ≤ D
    · obtain ⟨step_pairs, hlen1, hmem1, hchain1, hgrow⟩ :=
        compact_phase2_step A u0 D R h b hh hR192 hRD hA_int hA_mod hA_card
      let R1 : ℕ := R + (step_pairs.map Prod.snd).sum
      obtain ⟨rest, hlen2, hmem2, hchain2, hor⟩ := ih R1 (by omega)
      refine ⟨step_pairs ++ rest, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hlen1]
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hmem1 x hx1
        · exact hmem2 x hx2
      · exact StepGapChain.append Prod.snd h R step_pairs rest hchain1 hchain2
      · rw [List.map_append, List.sum_append, ← Nat.add_assoc]
        rcases hor with hgt | hpow
        · exact Or.inl hgt
        · right
          have h1 : (R * 31) * 31 ^ k ≤ (R1 * 30) * 31 ^ k :=
            Nat.mul_le_mul_right (31 ^ k) (by omega)
          have h2 : (R1 * 31 ^ k) * 30 ≤ ((R1 + (rest.map Prod.snd).sum) * 30 ^ k) * 30 :=
            Nat.mul_le_mul_right 30 hpow
          calc
            R * 31 ^ (k + 1) = (R * 31) * 31 ^ k := by ring
            _ ≤ (R1 * 30) * 31 ^ k := h1
            _ = (R1 * 31 ^ k) * 30 := by ring
            _ ≤ ((R1 + (rest.map Prod.snd).sum) * 30 ^ k) * 30 := h2
            _ = (R1 + (rest.map Prod.snd).sum) * 30 ^ (k + 1) := by ring
    · exact ⟨[], by simp, by simp, StepGapChain.nil R, Or.inl (by simpa using lt_of_not_ge hRD)⟩

/-- Construct T75 targets via the compact two-phase chain (`C = 24`, `979 + 6 * k1 ≤ n`). -/
theorem t75_compact_targets_from_supplies
    {n h b b_w k1 : ℕ} (hn_pos : 0 < n) (hn : Odd n)
    (hk1 : 979 + 6 * k1 ≤ n)
    (hh : h ∈ t75FavorableGaps)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hyD_gt : (2 : ℝ) < y - D)
    (hD_lo : 3072 * (h : ℝ) ≤ D)
    (hD_upper : D * (65 : ℝ) ^ k1 < (16 * 104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ k1)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y - D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y + D)
    (r0 : ℕ) (hr0_prime : Nat.Prime r0) (hr0h_prime : Nat.Prime (r0 + h))
    (hr0_lo : y - D / 2 ≤ (r0 : ℝ)) (hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2)
    (A : Finset ℕ) (hA_prime : ∀ p ∈ A, Nat.Prime p)
    (hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card_ge : 2 ≤ A.card) (hA_card : D < 24 * (h : ℝ) * (A.card : ℝ))
    (uw vw : ℕ) (huw_prime : Nat.Prime uw) (hvw_prime : Nat.Prime vw)
    (huw_mod : uw % h = b_w) (hvw_mod : vw % h = b_w)
    (huw_int : y - D ≤ (uw : ℝ) ∧ (uw : ℝ) ≤ y - D / 2)
    (hvw_int : y + D / 2 ≤ (vw : ℝ) ∧ (vw : ℝ) ≤ y + D) :
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  have hh_pos : 0 < h := by
    have hh' := hh
    simp only [t75FavorableGaps, Finset.mem_insert, Finset.mem_singleton] at hh'
    omega
  have hD_nonneg : 0 ≤ D := by
    have : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    linarith
  have hA_int_shift : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ (y - D / 2) + D := by
    intro p hp
    exact ⟨(hA_int p hp).1, by linarith [(hA_int p hp).2]⟩
  obtain ⟨ch1, hlen1, hmem1, hsc1, hor1⟩ :=
    compact_phase1_loop k1 A (y - D / 2) D (104 * h) h b hh_pos (le_refl _) hA_int_shift hA_mod hA_card
  let R1 : ℕ := 104 * h + (ch1.map Prod.snd).sum
  have hD16_lt_R1 : D / 16 < (R1 : ℝ) := by
    rcases hor1 with hgt | hpow
    · exact hgt
    · have hpowR : (104 : ℝ) * (h : ℝ) * (69 : ℝ) ^ k1 ≤ (R1 : ℝ) * (65 : ℝ) ^ k1 := by
        have hc : ((104 * h * 69 ^ k1 : ℕ) : ℝ) ≤ ((R1 * 65 ^ k1 : ℕ) : ℝ) := Nat.cast_le.mpr hpow
        push_cast at hc
        linarith
      have h65_pos : (0 : ℝ) < (65 : ℝ) ^ k1 := by positivity
      have hlt : (D / 16) * (65 : ℝ) ^ k1 < (R1 : ℝ) * (65 : ℝ) ^ k1 := by linarith
      exact lt_of_mul_lt_mul_right hlt h65_pos.le
  have hR1_192 : 192 * h ≤ R1 := by
    have hlt : ((192 * h : ℕ) : ℝ) < (R1 : ℝ) := by
      push_cast
      linarith
    exact (Nat.cast_lt.mp hlt).le
  obtain ⟨ch2, hlen2, hmem2, hsc2, hor2⟩ :=
    compact_phase2_loop 85 A (y - D / 2) D R1 h b hh_pos hR1_192 hA_int_shift hA_mod hA_card
  let R2 : ℕ := R1 + (ch2.map Prod.snd).sum
  have hD_lt_R2 : D < (R2 : ℝ) := by
    rcases hor2 with hgt | hpow
    · exact hgt
    · have h31 : (16 : ℝ) * (30 : ℝ) ^ 85 ≤ (31 : ℝ) ^ 85 := by norm_num
      have hpowR : (R1 : ℝ) * (31 : ℝ) ^ 85 ≤ (R2 : ℝ) * (30 : ℝ) ^ 85 := by
        have hc : ((R1 * 31 ^ 85 : ℕ) : ℝ) ≤ ((R2 * 30 ^ 85 : ℕ) : ℝ) := Nat.cast_le.mpr hpow
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hc
      have hm1 : (R1 : ℝ) * ((16 : ℝ) * (30 : ℝ) ^ 85) ≤ (R2 : ℝ) * (30 : ℝ) ^ 85 :=
        (mul_le_mul_of_nonneg_left h31 (Nat.cast_nonneg R1)).trans hpowR
      have hm2 : D * (30 : ℝ) ^ 85 < (R1 : ℝ) * ((16 : ℝ) * (30 : ℝ) ^ 85) := by
        have h30 : (0 : ℝ) < (30 : ℝ) ^ 85 := by positivity
        have hlt16 : D < 16 * (R1 : ℝ) := by linarith
        have hm := mul_lt_mul_of_pos_right hlt16 h30
        linarith
      exact lt_of_mul_lt_mul_right (lt_of_lt_of_le hm2 hm1) (by positivity)
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hpmin, hpmax, hle, hdvd, hspread⟩ :=
    mod_spread_ge_card_sub_one_mul A h b hh_pos hAne hA_mod
  let p_min := A.min' hAne
  let p_max := A.max' hAne
  let d_max := p_max - p_min
  have hdmax_pos : 0 < d_max := by
    have : 1 * h ≤ (A.card - 1) * h := Nat.mul_le_mul_right h (by omega)
    omega
  have hdmax_le_R2 : d_max ≤ R2 := by
    have hcast : (d_max : ℝ) = (p_max : ℝ) - (p_min : ℝ) := Nat.cast_sub hle
    have hleD : (d_max : ℝ) ≤ D := by linarith [(hA_int p_min hpmin).1, (hA_int p_max hpmax).2]
    have : (d_max : ℝ) ≤ (R2 : ℝ) := by linarith
    exact_mod_cast this
  let top := List.replicate 50 (p_min, d_max)
  have hsc_top : StepGapChain Prod.snd h R2 top :=
    StepGapChain.replicate Prod.snd h R2 50 (p_min, d_max) hdvd (by dsimp; omega)
  let chain_narrow := (ch1 ++ ch2) ++ top
  have hchain_narrow : StepGapChain Prod.snd h (104 * h) chain_narrow := by
    have h12 : StepGapChain Prod.snd h (104 * h) (ch1 ++ ch2) :=
      StepGapChain.append Prod.snd h (104 * h) ch1 ch2 hsc1 hsc2
    refine StepGapChain.append Prod.snd h (104 * h) (ch1 ++ ch2) top h12 ?_
    rw [List.map_append, List.sum_append, ← Nat.add_assoc]
    exact hsc_top
  have hmem_narrow : ∀ x ∈ chain_narrow, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx12 | hx3
    · rcases List.mem_append.mp hx12 with hx1 | hx2
      · exact hmem1 x hx1
      · exact hmem2 x hx2
    · rcases List.mem_replicate.mp hx3 with ⟨_, rfl⟩
      refine ⟨hpmin, ?_, hdmax_pos, hdvd⟩
      dsimp only
      have : p_min + d_max = p_max := by omega
      rw [this]
      exact hpmax
  have hPW_le : 3 * (104 + chain_narrow.length) + 7 ≤ n := by
    have hlen : chain_narrow.length = ch1.length + ch2.length + 50 := by
      simp only [chain_narrow, top, List.length_append, List.length_replicate]
    omega
  have hR_two_D : 2 * D ≤ ((104 * h + (chain_narrow.map Prod.snd).sum : ℕ) : ℝ) := by
    have hm1 : 48 * ((A.card - 1) * h) ≤ 48 * d_max := Nat.mul_le_mul_left 48 hspread
    have hm2 : 24 * A.card ≤ 48 * (A.card - 1) := by omega
    have hm3 : 24 * A.card * h ≤ 48 * (A.card - 1) * h := Nat.mul_le_mul_right h hm2
    have h24_le : 24 * A.card * h ≤ 50 * d_max := by
      have : 48 * (A.card - 1) * h = 48 * ((A.card - 1) * h) := by ring
      omega
    have h24_real : 24 * (h : ℝ) * (A.card : ℝ) ≤ ((50 * d_max : ℕ) : ℝ) := by
      have hc : ((24 * A.card * h : ℕ) : ℝ) ≤ ((50 * d_max : ℕ) : ℝ) := Nat.cast_le.mpr h24_le
      push_cast at hc ⊢
      linarith
    have hsum_eq : 104 * h + (chain_narrow.map Prod.snd).sum = R2 + 50 * d_max := by
      simp only [chain_narrow, top, List.map_append, List.sum_append, map_sum_replicate]
      dsimp [R2, R1]
      omega
    rw [hsum_eq, Nat.cast_add]
    linarith
  obtain ⟨m, narrow, wide, seed, low, gap, labels, hm, hdis, hcount, hlen, hprime, hwindow, hS,
    hseed_gap, hnodup, hfresh, hchain, hnarrow_mid, hwide_mid, hgap_wide⟩ :=
    package_seed_and_narrow_chain hh_pos (by decide) y D r0 hr0_prime hr0h_prime hr0_lo hr0_hi
      A hA_prime hA_int chain_narrow hPW_le hmem_narrow hchain_narrow hR_two_D
      uw vw huw_prime hvw_prime huw_mod hvw_mod huw_int hvw_int
  exact t75_targets_from_seed_chain_general hn_pos hn hm hh narrow wide low gap hdis hcount hlen
    y D hy hD_nonneg hyD_gt hsupply hprime hwindow seed labels hS hseed_gap hnodup hfresh hchain
    hnarrow_mid hwide_mid hgap_wide

/-! ### Part 2: General `(C, k)` doubling chain (`9301 ≤ n ≤ 19483` and `35735 ≤ n < ∞`) -/

private theorem general_double_step (C : ℕ) (hC : 1 ≤ C)
    (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hRC : 2 * C * h ≤ R) (hRD : (R : ℝ) ≤ D)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < (C : ℝ) * (h : ℝ) * (A.card : ℝ)) :
    ∃ step_pairs : List (ℕ × ℕ),
      step_pairs.length = 4 * C ∧
      (∀ x ∈ step_pairs, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R step_pairs ∧
      2 * R < R + (step_pairs.map Prod.snd).sum := by
  have h2Ch_pos : 0 < 2 * C * h := Nat.mul_pos (by omega) hh
  have hRpos : 0 < R := lt_of_lt_of_le h2Ch_pos hRC
  have hRposR : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hRpos
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le hRposR hRD
  have h2ChR_pos : (0 : ℝ) < 2 * (C : ℝ) * (h : ℝ) := by exact_mod_cast h2Ch_pos
  let q : ℕ := R / (2 * C * h)
  have hq1 : 1 ≤ q := Nat.div_pos hRC h2Ch_pos
  have hcard : (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card := by
    have hdiv1 : (1 : ℝ) ≤ D / (R : ℝ) := (one_le_div hRposR).mpr hRD
    have hfl : ((⌊D / (R : ℝ)⌋₊ : ℕ) : ℝ) ≤ D / (R : ℝ) := Nat.floor_le (by positivity)
    have hK_le : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (D / (R : ℝ)) := by
      push_cast
      linarith
    have hq_nat : q * (2 * C * h) ≤ R := Nat.div_mul_le_self R (2 * C * h)
    have hq_real : (q : ℝ) * (2 * (C : ℝ) * (h : ℝ)) ≤ (R : ℝ) := by exact_mod_cast hq_nat
    have hm1 := mul_le_mul_of_nonneg_right hK_le
      (show (0 : ℝ) ≤ (q : ℝ) * (2 * (C : ℝ) * (h : ℝ)) by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hq_real (show (0 : ℝ) ≤ 2 * (D / (R : ℝ)) by positivity)
    have hmul : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) * ((q : ℝ) * (2 * (C : ℝ) * (h : ℝ))) ≤ 2 * D := by
      have hc : (2 * (D / (R : ℝ))) * (R : ℝ) = 2 * D := by
        rw [mul_assoc, div_mul_cancel₀ _ hRposR.ne']
      linarith
    have hlt_real : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) < (A.card : ℝ) := by
      have hprod : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) * (2 * (C : ℝ) * (h : ℝ)) <
          (A.card : ℝ) * (2 * (C : ℝ) * (h : ℝ)) := by
        push_cast at hmul ⊢
        linarith
      exact lt_of_mul_lt_mul_right hprod h2ChR_pos.le
    exact_mod_cast hlt_real
  obtain ⟨p_min, p_max, hpmin, hpmax, hle, hdvd, hq_le, hgap_le⟩ :=
    pigeonhole_spatial_bin A u0 D R h b q hh hRpos hq1 hA_int hA_mod hcard
  let d : ℕ := p_max - p_min
  have hd_pos : 0 < d := lt_of_lt_of_le (Nat.mul_pos hq1 hh) hq_le
  refine ⟨List.replicate (4 * C) (p_min, d), by simp, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    refine ⟨hpmin, ?_, hd_pos, hdvd⟩
    dsimp only
    have : p_min + d = p_max := by omega
    rw [this]
    exact hpmax
  · exact StepGapChain.replicate Prod.snd h R (4 * C) (p_min, d) hdvd (by dsimp; omega)
  · rw [map_sum_replicate]
    dsimp only
    have hdiv_mod := (Nat.div_add_mod R (2 * C * h)).symm
    have hmod_lt : R % (2 * C * h) < 2 * C * h := Nat.mod_lt R h2Ch_pos
    have hR_lt : R < (2 * C * h) * (q + 1) := by
      change R < (2 * C * h) * (R / (2 * C * h) + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h2q : (2 * C * h) * (q + 1) ≤ (4 * C) * (q * h) := by
      have hq2 : q + 1 ≤ 2 * q := by omega
      calc
        (2 * C * h) * (q + 1) ≤ (2 * C * h) * (2 * q) := Nat.mul_le_mul_left _ hq2
        _ = (4 * C) * (q * h) := by ring
    have h4Cd : (4 * C) * (q * h) ≤ (4 * C) * d := Nat.mul_le_mul_left (4 * C) hq_le
    omega

private theorem general_double_loop (C k : ℕ) (hC : 1 ≤ C)
    (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hRC : 2 * C * h ≤ R)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < (C : ℝ) * (h : ℝ) * (A.card : ℝ)) :
    ∃ chain : List (ℕ × ℕ),
      chain.length ≤ 4 * C * k ∧
      (∀ x ∈ chain, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R chain ∧
      (D < ((R + (chain.map Prod.snd).sum : ℕ) : ℝ) ∨
        R * 2 ^ k ≤ R + (chain.map Prod.snd).sum) := by
  induction k generalizing R with
  | zero =>
    refine ⟨[], by simp, by simp, StepGapChain.nil R, Or.inr (by simp)⟩
  | succ k ih =>
    by_cases hRD : (R : ℝ) ≤ D
    · obtain ⟨step_pairs, hlen1, hmem1, hchain1, hdouble⟩ :=
        general_double_step C hC A u0 D R h b hh hRC hRD hA_int hA_mod hA_card
      let R1 : ℕ := R + (step_pairs.map Prod.snd).sum
      obtain ⟨rest, hlen2, hmem2, hchain2, hor⟩ := ih R1 (by omega)
      refine ⟨step_pairs ++ rest, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hlen1]
        have : 4 * C + 4 * C * k = 4 * C * (k + 1) := by ring
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hmem1 x hx1
        · exact hmem2 x hx2
      · exact StepGapChain.append Prod.snd h R step_pairs rest hchain1 hchain2
      · rw [List.map_append, List.sum_append, ← Nat.add_assoc]
        rcases hor with hgt | hpow
        · exact Or.inl hgt
        · right
          calc
            R * 2 ^ (k + 1) = (2 * R) * 2 ^ k := by ring
            _ ≤ R1 * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) (by omega)
            _ ≤ R1 + (rest.map Prod.snd).sum := hpow
    · exact ⟨[], by simp, by simp, StepGapChain.nil R, Or.inl (by simpa using lt_of_not_ge hRD)⟩

/-- Construct T75 targets via the general `(C, k)` doubling chain (`1 ≤ C`). -/
theorem t75_general_targets_from_supplies
    {n h b b_w C k : ℕ} (hn_pos : 0 < n) (hn : Odd n)
    (hC : 1 ≤ C)
    (hPW_bound : 3 * (4 * C * (k + 1) + 2) + 7 ≤ n)
    (hh : h ∈ t75FavorableGaps)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD_nonneg : 0 ≤ D) (hyD_gt : (2 : ℝ) < y - D)
    (hD_upper : D < ((2 * C * h * 2 ^ k : ℕ) : ℝ))
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y - D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y + D)
    (r0 : ℕ) (hr0_prime : Nat.Prime r0) (hr0h_prime : Nat.Prime (r0 + h))
    (hr0_lo : y - D / 2 ≤ (r0 : ℝ)) (hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2)
    (A : Finset ℕ) (hA_prime : ∀ p ∈ A, Nat.Prime p)
    (hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card_ge : 2 ≤ A.card) (hA_card : D < (C : ℝ) * (h : ℝ) * (A.card : ℝ))
    (uw vw : ℕ) (huw_prime : Nat.Prime uw) (hvw_prime : Nat.Prime vw)
    (huw_mod : uw % h = b_w) (hvw_mod : vw % h = b_w)
    (huw_int : y - D ≤ (uw : ℝ) ∧ (uw : ℝ) ≤ y - D / 2)
    (hvw_int : y + D / 2 ≤ (vw : ℝ) ∧ (vw : ℝ) ≤ y + D) :
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  have hh_pos : 0 < h := by
    have hh' := hh
    simp only [t75FavorableGaps, Finset.mem_insert, Finset.mem_singleton] at hh'
    omega
  have hA_int_shift : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ (y - D / 2) + D := by
    intro p hp
    exact ⟨(hA_int p hp).1, by linarith [(hA_int p hp).2]⟩
  obtain ⟨ch1, hlen1, hmem1, hsc1, hor1⟩ :=
    general_double_loop C k hC A (y - D / 2) D (2 * C * h) h b hh_pos (le_refl _)
      hA_int_shift hA_mod hA_card
  let R1 : ℕ := 2 * C * h + (ch1.map Prod.snd).sum
  have hD_lt_R1 : D < (R1 : ℝ) := by
    rcases hor1 with hgt | hpow
    · exact hgt
    · have hpowR : ((2 * C * h * 2 ^ k : ℕ) : ℝ) ≤ (R1 : ℝ) := Nat.cast_le.mpr hpow
      linarith
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hpmin, hpmax, hle, hdvd, hspread⟩ :=
    mod_spread_ge_card_sub_one_mul A h b hh_pos hAne hA_mod
  let p_min := A.min' hAne
  let p_max := A.max' hAne
  let d_max := p_max - p_min
  have hdmax_pos : 0 < d_max := lt_of_lt_of_le (Nat.mul_pos (by omega) hh_pos) hspread
  have hdmax_le_R1 : d_max ≤ R1 := by
    have hcast : (d_max : ℝ) = (p_max : ℝ) - (p_min : ℝ) := Nat.cast_sub hle
    have hleD : (d_max : ℝ) ≤ D := by linarith [(hA_int p_min hpmin).1, (hA_int p_max hpmax).2]
    have : (d_max : ℝ) ≤ (R1 : ℝ) := by linarith
    exact_mod_cast this
  let top := List.replicate (2 * C + 2) (p_min, d_max)
  have hsc_top : StepGapChain Prod.snd h R1 top :=
    StepGapChain.replicate Prod.snd h R1 (2 * C + 2) (p_min, d_max) hdvd (by dsimp; omega)
  let chain_narrow := ch1 ++ top
  have hchain_narrow : StepGapChain Prod.snd h (2 * C * h) chain_narrow :=
    StepGapChain.append Prod.snd h (2 * C * h) ch1 top hsc1 hsc_top
  have hmem_narrow : ∀ x ∈ chain_narrow, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hmem1 x hx1
    · rcases List.mem_replicate.mp hx2 with ⟨_, rfl⟩
      refine ⟨hpmin, ?_, hdmax_pos, hdvd⟩
      dsimp only
      have : p_min + d_max = p_max := by omega
      rw [this]
      exact hpmax
  have hPW_le : 3 * (2 * C + chain_narrow.length) + 7 ≤ n := by
    have hlen : chain_narrow.length = ch1.length + (2 * C + 2) := by simp [chain_narrow, top]
    have hle1 : 2 * C + chain_narrow.length ≤ 4 * C * (k + 1) + 2 := by
      have : 2 * C + (4 * C * k + (2 * C + 2)) = 4 * C * (k + 1) + 2 := by ring
      omega
    omega
  have hR_two_D : 2 * D ≤ ((2 * C * h + (chain_narrow.map Prod.snd).sum : ℕ) : ℝ) := by
    have hm1 : (2 * C + 2) * ((A.card - 1) * h) ≤ (2 * C + 2) * d_max :=
      Nat.mul_le_mul_left (2 * C + 2) hspread
    have hm2 : A.card ≤ 2 * (A.card - 1) := by omega
    have hm3 : C * A.card ≤ (2 * C + 2) * (A.card - 1) := by
      calc
        C * A.card ≤ C * (2 * (A.card - 1)) := Nat.mul_le_mul_left C hm2
        _ = (2 * C) * (A.card - 1) := by ring
        _ ≤ (2 * C + 2) * (A.card - 1) := Nat.mul_le_mul_right _ (by omega)
    have hC_le : C * A.card * h ≤ (2 * C + 2) * d_max := by
      have hm4 : C * A.card * h ≤ (2 * C + 2) * (A.card - 1) * h := Nat.mul_le_mul_right h hm3
      have heq : (2 * C + 2) * (A.card - 1) * h = (2 * C + 2) * ((A.card - 1) * h) := by ring
      omega
    have hC_real : (C : ℝ) * (h : ℝ) * (A.card : ℝ) ≤ (((2 * C + 2) * d_max : ℕ) : ℝ) := by
      have hc : ((C * A.card * h : ℕ) : ℝ) ≤ (((2 * C + 2) * d_max : ℕ) : ℝ) := Nat.cast_le.mpr hC_le
      push_cast at hc ⊢
      linarith
    have hsum_eq : 2 * C * h + (chain_narrow.map Prod.snd).sum = R1 + (2 * C + 2) * d_max := by
      simp only [chain_narrow, top, List.map_append, List.sum_append, map_sum_replicate]
      dsimp [R1]
      omega
    rw [hsum_eq, Nat.cast_add]
    linarith
  obtain ⟨m, narrow, wide, seed, low, gap, labels, hm, hdis, hcount, hlen, hprime, hwindow, hS,
    hseed_gap, hnodup, hfresh, hchain, hnarrow_mid, hwide_mid, hgap_wide⟩ :=
    package_seed_and_narrow_chain hh_pos (by omega) y D r0 hr0_prime hr0h_prime hr0_lo hr0_hi
      A hA_prime hA_int chain_narrow hPW_le hmem_narrow hchain_narrow hR_two_D
      uw vw huw_prime hvw_prime huw_mod hvw_mod huw_int hvw_int
  exact t75_targets_from_seed_chain_general hn_pos hn hm hh narrow wide low gap hdis hcount hlen
    y D hy hD_nonneg hyD_gt hsupply hprime hwindow seed labels hS hseed_gap hnodup hfresh hchain
    hnarrow_mid hwide_mid hgap_wide

end

end Sude
