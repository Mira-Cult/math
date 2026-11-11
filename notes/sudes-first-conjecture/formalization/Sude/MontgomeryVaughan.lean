import Sude.APInterval

/-! Exact published short-progression hypothesis and finite-set adaptation.
Montgomery--Vaughan, The large sieve, Mathematika 20 (1973), Theorem 2,
(1.10), printed p. 121. This is a hypothesis, not an axiom or a proof of the
published theorem. See import-map.json for the source and precise domain. -/
namespace Sude
noncomputable section

/-- Theorem 2 (1.10), with `(x,x+y]` counted by the exact finite interval.
All variables and strict domain conditions match the published statement. -/
def MVBrunTitchmarsh : Prop := ∀ (x y : ℝ) (k a : ℕ),
  0 < x → 0 < y → 0 < k → 0 < a → Nat.Coprime k a → (k : ℝ) < y →
    ((apInterval x (x + y) k (a : ℤ)).card : ℝ) <
      2 * y / ((Nat.totient k : ℝ) * Real.log (y / k))

/-- BT3's upper bound applies to any subset of the published interval;
prior deletions cannot increase its neighbour count. The logarithmic
threshold and the positive denominator are proved in the adaptation. -/
theorem mv_short_interval_subset_bound (mv : MVBrunTitchmarsh)
    (x y ell : ℝ) (k a : ℕ) (candidates : Finset ℕ)
    (hx : 0 < x) (hy : 0 < y) (hk : 0 < k) (ha : 0 < a)
    (hcoprime : Nat.Coprime k a) (hyk : (k : ℝ) < y)
    (hell : 0 < ell) (hexp : Real.exp ell ≤ y / k)
    (hsub : candidates ⊆ apInterval x (x + y) k (a : ℤ)) :
    (candidates.card : ℝ) < 2 * y / ((Nat.totient k : ℝ) * ell) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hdiv : 0 < y / k := div_pos hy hkreal
  have hlog : ell ≤ Real.log (y / k) := (Real.le_log_iff_exp_le hdiv).2 hexp
  have hphi : (0 : ℝ) < Nat.totient k := by exact_mod_cast (Nat.totient_pos.mpr hk)
  have hden : (Nat.totient k : ℝ) * ell ≤ (Nat.totient k : ℝ) * Real.log (y / k) :=
    mul_le_mul_of_nonneg_left hlog hphi.le
  have hratio : 2 * y / ((Nat.totient k : ℝ) * Real.log (y / k)) ≤
      2 * y / ((Nat.totient k : ℝ) * ell) := by
    exact div_le_div_of_nonneg_left (by positivity) (mul_pos hphi hell) hden
  have hc : (candidates.card : ℝ) ≤ (apInterval x (x + y) k (a : ℤ)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (hc.trans_lt (mv x y k a hx hy hk ha hcoprime hyk)).trans_le hratio

/-- Actual surviving upper neighbours in a reduced progression, at positive
gap no larger than the specified real width. -/
def shortClassNeighbours (unused : Finset ℕ) (p k a : ℕ) (width : ℝ) : Finset ℕ :=
  unused.filter fun q => p < q ∧ (q : ℝ) ≤ p + width ∧ (q : ℤ) % k = (a : ℤ) % k

/-- BT3 applied to the actual surviving prime set. No independence or
assumption about the deleted entries is used. -/
theorem mv_depleted_neighbour_bound (mv : MVBrunTitchmarsh)
    (unused : Finset ℕ) (p k a : ℕ) (width ell : ℝ)
    (hprimes : ∀ q ∈ unused, Nat.Prime q) (hp : 0 < p)
    (hk : 0 < k) (ha : 0 < a) (hcoprime : Nat.Coprime k a)
    (hwidth : (k : ℝ) < width) (hell : 0 < ell)
    (hexp : Real.exp ell ≤ width / k) :
    ((shortClassNeighbours unused p k a width).card : ℝ) <
      2 * width / ((Nat.totient k : ℝ) * ell) := by
  have hkreal : (0 : ℝ) < k := by exact_mod_cast hk
  have hwidthpos : 0 < width := lt_trans hkreal hwidth
  have hsub : shortClassNeighbours unused p k a width ⊆
      apInterval p (p + width) k (a : ℤ) := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2
    have hprime := hprimes q (Finset.mem_filter.mp hq).1
    apply (mem_apInterval_iff p (p + width) k (a : ℤ) (by positivity) (by positivity) q).2
    refine ⟨hprime, ?_, hq'.2.1, hq'.2.2⟩
    exact_mod_cast hq'.1
  exact mv_short_interval_subset_bound mv p width ell k a _ (by exact_mod_cast hp) hwidthpos
    hk ha hcoprime hwidth hell hexp hsub

/-- The BT2/BT3 choice of `ζ` converts the published neighbour upper bound
to the source's cancellation term, with all nonzero denominators explicit. -/
theorem mv_neighbour_radius_identity (ell φ g η M R classes X : ℝ)
    (hell : ell ≠ 0) (hφ : φ ≠ 0) (hg : g ≠ 0) :
    2 * ((ell * φ / (2 * g)) * g * (η * M * R / (classes * X) - 1 / 2)) /
        (φ * ell) = η * M * R / (classes * X) - 1 / 2 := by
  field_simp

end
end Sude
