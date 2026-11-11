import Sude.T75FineGridBinning
import Sude.FWT75NominalSeedChainTargets

/-!
# First-Band Nominal T75 Targets from Concrete Prime Supplies

Combines the band-independent `t75_seed_chain_package_from_supplies` (`T75FineGridBinning`)
with `fw_t75_nominal_targets_from_seed_chain` (`FWT75NominalSeedChainTargets`) to construct
nominal T75 prime targets for `19485 ≤ n ≤ 21248`.
-/

namespace Sude

noncomputable section

set_option maxHeartbeats 2000000

/-- Construct the nominal T75 targets for the first FW band (`19485 ≤ n ≤ 21248`, `Odd n`) from:
1. A seed pair `(r0, r0 + h)` in `[y - D/2, y + D/2]` with `h ∈ t75FavorableGaps`,
2. A central prime set `A ⊆ [y - D/2, y + D/2]` in one residue class mod `h` with
   `2 ≤ A.card` and `D < 20 * h * A.card`,
3. A wide prime pair `(uw, vw)` in `[y - 3*D/4, y - D/2] × [y + D/2, y + 3*D/4]`
   in one residue class mod `h`,
4. Unit-bracket prime supply on `[y - D, y]` and `[y, y + D]`. -/
theorem fw_t75_nominal_targets_from_supplies
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n h b b_w : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hn : Odd n)
    (hh : h ∈ t75FavorableGaps)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hDnominal : D = y / 1240)
    (hD_upper : D < ((72 * h * 2 ^ 32 : ℕ) : ℝ))
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y - D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y + D)
    (r0 : ℕ) (hr0_prime : Nat.Prime r0) (hr0h_prime : Nat.Prime (r0 + h))
    (hr0_lo : y - D / 2 ≤ (r0 : ℝ)) (hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2)
    (A : Finset ℕ) (hA_prime : ∀ p ∈ A, Nat.Prime p)
    (hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card_ge : 2 ≤ A.card) (hA_card : D < 36 * (h : ℝ) * (A.card : ℝ))
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
  have hn14269 : 14269 ≤ n := by omega
  obtain ⟨m, narrow, wide, seed, low, gap, labels, hm, hdis, hcount, hlen, hprime, hwindow, hS,
    hseed_gap, hnodup, hfresh, hchain, hnarrow_mid, hwide_mid, hgap_wide⟩ :=
    t75_seed_chain_package_from_supplies hn14269 hh_pos y D hD_upper r0 hr0_prime hr0h_prime
      hr0_lo hr0_hi A hA_prime hA_int hA_mod hA_card_ge hA_card uw vw huw_prime hvw_prime
      huw_mod hvw_mod huw_int hvw_int
  obtain ⟨_xs, _lo, _hi, _values, _chosen, _hlen_xs, _hsub, _hforall, _ht, f, _hf_get, hf_sum, hf_valid⟩ :=
    fw_t75_nominal_targets_from_seed_chain bmor lower upper hnlo hnhi hn hm hh narrow wide low gap
      hdis hcount hlen y D hy hDnominal hsupply hprime hwindow seed labels hS hseed_gap hnodup
      hfresh hchain hnarrow_mid hwide_mid hgap_wide
  exact ⟨f, hf_sum, hf_valid⟩

end

end Sude
