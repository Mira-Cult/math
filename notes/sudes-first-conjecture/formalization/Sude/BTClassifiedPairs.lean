import Sude.FiberPairCount
import Sude.BTShortPairCount

/-! Common-gap matching from actual finite bin/class partitions. -/
namespace Sude
noncomputable section

/-- BT2--BT5 for a proved finite partition into at most `B` bin/class
fibers. The key's physical gap and residue properties and the final scalar
gate are explicit; no pair-population lower bound is assumed. -/
theorem mv_common_gap_from_fiber_partition {K : Type*} [DecidableEq K]
    (mv : MVBrunTitchmarsh) (unused : Finset ℕ) (key : ℕ → K)
    (k g R Q B : ℕ) (residue : ℕ → ℕ) (width ell : ℝ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hclasses : ∀ p ∈ unused, 0 < residue p ∧ Nat.Coprime k (residue p))
    (hkey : ∀ p ∈ unused, ∀ q ∈ unused, p < q → key p = key q →
      g ∣ q - p ∧ q - p ≤ R ∧ (q : ℤ) % k = (residue p : ℤ) % k)
    (hB : (unused.image key).card ≤ B) (hBpos : 0 < B)
    (hk : 0 < k) (hg : 0 < g) (hwidth : (k : ℝ) < width)
    (hell : 0 < ell) (hexp : Real.exp ell ≤ width / k)
    (hgate : (((R / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient k : ℝ) * ell)) ≤
        ((unused.card : ℝ) ^ 2 / B - unused.card) / 2) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ R ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, p ∈ unused ∧ p + h ∈ unused ∧ key p = key (p + h)) ∧
      PairwiseDisjointPairs T h := by
  classical
  let P := sameClassPairs unused key
  have hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      (z.2 : ℤ) % k = (residue z.1 : ℤ) % k := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hpq := Finset.mem_product.mp hz'.1
    exact ⟨hpq.1, hpq.2, hz'.2.1, (hkey z.1 hpq.1 z.2 hpq.2 hz'.2.1 hz'.2.2).2.2⟩
  have hgaps : ∀ z ∈ P, g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hpq := Finset.mem_product.mp hz'.1
    have h := hkey z.1 hpq.1 z.2 hpq.2 hz'.2.1 hz'.2.2
    exact ⟨h.1, h.2.1⟩
  have hpairCount := sameClassPairs_lower_bound unused key B hB hBpos
  have hpopulation : (((R / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient k : ℝ) * ell)) ≤ P.card :=
    hgate.trans hpairCount
  obtain ⟨h, T, hh, hdiv, hR, hD, hQ, hT, hmatch⟩ :=
    mv_multiclass_common_gap_from_pair_population mv unused P k g R Q residue width ell
      hne hprimes hpairs hgaps hk hg hclasses hwidth hell hexp hpopulation
  refine ⟨h, T, hh, hdiv, hR, hD, hQ, ?_, hmatch⟩
  intro p hp
  have hp' := hT p hp
  have hkeyeq := (Finset.mem_filter.mp hp'.1).2.2
  exact ⟨hp'.2.1, hp'.2.2, hkeyeq⟩

end
end Sude
