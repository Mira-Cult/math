import Sude.BTIntervalBins

/-! Elementary short-pair counting for the initial AP phase. -/
namespace Sude
noncomputable section

/-- At a fixed lower endpoint, positive gaps divisible by `g` and strictly
below `width` give fewer than `width/g` candidate pairs. No primality or
progression estimate is used. -/
theorem ap_short_fiber_bound (P : Finset (ℕ × ℕ)) (p g : ℕ) (width : ℝ)
    (hg : 0 < g) (hwidth : 0 < width)
    (hvalid : ∀ z ∈ P, z.1 < z.2 ∧ g ∣ z.2 - z.1) :
    (((shortPairSet P width).filter fun z => z.1 = p).card : ℝ) < width / g := by
  classical
  let F := (shortPairSet P width).filter fun z => z.1 = p
  let C := ⌈width / g⌉₊
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hx : 0 < width / g := div_pos hwidth hgR
  have hC : 0 < C := Nat.ceil_pos.mpr hx
  have hk (z : ℕ × ℕ) (hz : z ∈ F) :
      0 < (z.2 - z.1) / g ∧ (z.2 - z.1) / g < C := by
    have hz' := Finset.mem_filter.mp hz
    have hzshort := Finset.mem_filter.mp hz'.1
    have hv := hvalid z hzshort.1
    have hgap : 0 < z.2 - z.1 := by omega
    have hm := Nat.div_mul_cancel hv.2
    have hkpos : 0 < (z.2 - z.1) / g := by
      by_contra hn
      have he : (z.2 - z.1) / g = 0 := Nat.eq_zero_of_not_pos hn
      rw [he] at hm
      simp at hm
      omega
    have hmR : (((z.2 - z.1) / g : ℕ) : ℝ) * g = ((z.2 - z.1 : ℕ) : ℝ) := by
      exact_mod_cast hm
    have hklt : (((z.2 - z.1) / g : ℕ) : ℝ) < width / g := by
      apply (lt_div_iff₀ hgR).2
      linarith [hzshort.2]
    exact ⟨hkpos, Nat.lt_ceil.mpr hklt⟩
  have hcard : F.card ≤ C - 1 := by
    have hc : F.card ≤ (Finset.range (C - 1)).card := by
      apply Finset.card_le_card_of_injOn (fun z : ℕ × ℕ => (z.2 - z.1) / g - 1)
      · intro z hz
        apply Finset.mem_range.mpr
        have ⟨hpos, hlt⟩ := hk z hz
        dsimp only
        omega
      · intro x hx y hy he
        have hfx := (Finset.mem_filter.mp hx).2
        have hfy := (Finset.mem_filter.mp hy).2
        have hPx := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
        have hPy := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1
        have ⟨hkx, _⟩ := hk x hx
        have ⟨hky, _⟩ := hk y hy
        dsimp only at he
        have heq : (x.2 - x.1) / g = (y.2 - y.1) / g := by omega
        have hm := congrArg (fun k : ℕ => k * g) heq
        rw [Nat.div_mul_cancel (hvalid x hPx).2, Nat.div_mul_cancel (hvalid y hPy).2] at hm
        apply Prod.ext
        · omega
        · have hxlt := (hvalid x hPx).1
          have hylt := (hvalid y hPy).1
          omega
    simpa using hc
  have hcast : ((F.card : ℕ) : ℝ) ≤ (C : ℝ) - 1 := by
    have hcast' : (F.card : ℝ) ≤ (C - 1 : ℕ) := by exact_mod_cast hcard
    simpa only [Nat.cast_sub (by omega : 1 ≤ C), Nat.cast_one] using hcast'
  have hceil : (C : ℝ) < width / g + 1 := Nat.ceil_lt_add_one hx.le
  exact lt_of_le_of_lt hcast (by linarith)

/-- Summing over actual lower endpoints gives the elementary short-pair
charge used before the BT phase starts. -/
theorem ap_short_pair_count (unused : Finset ℕ) (P : Finset (ℕ × ℕ))
    (g : ℕ) (width : ℝ) (hne : unused.Nonempty) (hg : 0 < g) (hwidth : 0 < width)
    (hvalid : ∀ z ∈ P, z.1 ∈ unused ∧ z.1 < z.2 ∧ g ∣ z.2 - z.1) :
    ((shortPairSet P width).card : ℝ) < (unused.card : ℝ) * (width / g) := by
  classical
  let short := shortPairSet P width
  let fiber : ℕ → Finset (ℕ × ℕ) := fun p => short.filter fun z => z.1 = p
  have hmap : ∀ z ∈ short, z.1 ∈ unused := by
    intro z hz
    exact (hvalid z (Finset.mem_filter.mp hz).1).1
  have hcount : short.card = ∑ p ∈ unused, (fiber p).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := short) (t := unused) (f := Prod.fst) hmap
  have hlt : ∀ p ∈ unused, ((fiber p).card : ℝ) < width / g := by
    intro p hp
    exact ap_short_fiber_bound P p g width hg hwidth (fun z hz => (hvalid z hz).2)
  have hsum := Finset.sum_lt_sum_of_nonempty hne hlt
  have hcountR : (short.card : ℝ) = ∑ p ∈ unused, ((fiber p).card : ℝ) := by exact_mod_cast hcount
  rw [← hcountR] at hsum
  simpa [short] using hsum

/-- The elementary charge leaves enough pairs for a common-gap matching,
with actual distinct endpoints. -/
theorem ap_common_gap_from_pair_population (unused : Finset ℕ) (P : Finset (ℕ × ℕ))
    (g R Q : ℕ) (width : ℝ) (hne : unused.Nonempty) (hg : 0 < g) (hwidth : 0 < width)
    (hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R)
    (hpopulation : (((R / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (width / g) ≤ P.card) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ R ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, p ∈ unused ∧ p + h ∈ unused) ∧ PairwiseDisjointPairs T h := by
  classical
  let short := shortPairSet P width
  let long := P.filter fun z => width ≤ ((z.2 - z.1 : ℕ) : ℝ)
  have hpartition : short.card + long.card = P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := P)
      (fun z => ((z.2 - z.1 : ℕ) : ℝ) < width)
    have heq : P.filter (fun z => ¬ ((z.2 - z.1 : ℕ) : ℝ) < width) = long := by
      ext z
      simp [long, not_lt]
    rw [heq] at h
    exact h
  have hpartitionR : (short.card : ℝ) + long.card = P.card := by exact_mod_cast hpartition
  have hshort := ap_short_pair_count unused P g width hne hg hwidth
    (fun z hz => ⟨(hpairs z hz).1, (hpairs z hz).2.2.1, (hpairs z hz).2.2.2.1⟩)
  have hcountR : (((R / g) * (2 * Q) : ℕ) : ℝ) < long.card := by linarith
  have hcount : (R / g) * (2 * Q) < long.card := by exact_mod_cast hcountR
  have hvalid : ∀ z ∈ long, z.1 < z.2 ∧ g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R ∧
      width ≤ ((z.2 - z.1 : ℕ) : ℝ) := by
    intro z hz
    have hzP := (Finset.mem_filter.mp hz).1
    exact ⟨(hpairs z hzP).2.2.1, (hpairs z hzP).2.2.2.1, (hpairs z hzP).2.2.2.2,
      (Finset.mem_filter.mp hz).2⟩
  obtain ⟨h, T, hh, hdiv, hR, hD, hQ, hT, hmatch⟩ :=
    common_gap_matching_from_pairs long g R Q width hg hvalid hcount
  refine ⟨h, T, hh, hdiv, hR, hD, hQ, ?_, hmatch⟩
  intro p hp
  have hpP := (Finset.mem_filter.mp (hT p hp)).1
  exact ⟨(hpairs (p, p + h) hpP).1, (hpairs (p, p + h) hpP).2.1⟩

/-- Elementary AP selection from any finite partition with a proved class
count and physical gap properties. -/
theorem ap_common_gap_from_fiber_partition {K : Type*} [DecidableEq K]
    (unused : Finset ℕ) (key : ℕ → K) (g R Q B : ℕ) (width : ℝ)
    (hne : unused.Nonempty) (hg : 0 < g) (hwidth : 0 < width)
    (hkey : ∀ p ∈ unused, ∀ q ∈ unused, p < q → key p = key q →
      g ∣ q - p ∧ q - p ≤ R)
    (hB : (unused.image key).card ≤ B) (hBpos : 0 < B)
    (hgate : (((R / g) * (2 * Q) : ℕ) : ℝ) + (unused.card : ℝ) * (width / g) ≤
      ((unused.card : ℝ) ^ 2 / B - unused.card) / 2) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ R ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, p ∈ unused ∧ p + h ∈ unused) ∧ PairwiseDisjointPairs T h := by
  classical
  let P := sameClassPairs unused key
  have hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hpq := Finset.mem_product.mp hz'.1
    have h := hkey z.1 hpq.1 z.2 hpq.2 hz'.2.1 hz'.2.2
    exact ⟨hpq.1, hpq.2, hz'.2.1, h.1, h.2⟩
  have hpairCount := sameClassPairs_lower_bound unused key B hB hBpos
  exact ap_common_gap_from_pair_population unused P g R Q width hne hg hwidth hpairs
    (hgate.trans hpairCount)

/-- Initial AP phase on concrete interval/residue bins, without an analytic
progression theorem. The exact finite bin gate remains explicit. -/
theorem ap_common_gap_from_interval_classes (unused classes : Finset ℕ)
    (lo W radius width : ℝ) (g Q : ℕ)
    (hne : unused.Nonempty) (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + W)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hg : 0 < g) (hR : 0 < radius) (hwidth : 0 < width)
    (hgate : (((⌊radius⌋₊ / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (width / g) ≤
        ((unused.card : ℝ) ^ 2 / ((⌊W / radius⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊radius⌋₊ ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, p ∈ unused ∧ p + h ∈ unused) ∧ PairwiseDisjointPairs T h := by
  let key := progressionBinKey lo radius g
  let B := (⌊W / radius⌋₊ + 1) * classes.card
  have hB : (unused.image key).card ≤ B := progression_bin_key_card unused classes lo W radius g hR hinterval hclasses
  obtain ⟨p₀, hp₀⟩ := hne
  have hclassespos : 0 < classes.card := Finset.card_pos.mpr ⟨p₀ % g, hclasses p₀ hp₀⟩
  have hBpos : 0 < B := Nat.mul_pos (by omega) hclassespos
  have hkey : ∀ p ∈ unused, ∀ q ∈ unused, p < q → key p = key q →
      g ∣ q - p ∧ q - p ≤ ⌊radius⌋₊ := by
    intro p hp q hq hpq heq
    have h := progression_bin_key_pair hR (hinterval p hp).1 hpq heq
    exact ⟨h.1, h.2.1⟩
  exact ap_common_gap_from_fiber_partition unused key g ⌊radius⌋₊ Q B width
    ⟨p₀, hp₀⟩ hg hwidth hkey hB hBpos hgate

end
end Sude
