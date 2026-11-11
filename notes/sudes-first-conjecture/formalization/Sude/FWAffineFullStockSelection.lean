import Sude.FWAffineWheelPairSupply

/-! A larger-gap affine selector under an explicit gate on the actual stock.
The pair population is derived from the existing spatial bins and the AW2
short-pair bound; the numerical gate and threshold remain explicit. -/
namespace Sude
noncomputable section

/-- Given an actual screened stock and a positive real threshold D, the
binned-pair lower bound less the AW2 short charge pays the equal-gap matching
whenever the displayed actual-stock gate holds. No independent pair-population
hypothesis is assumed. -/
theorem fw_affine_common_gap_from_actual_stock_gate
    (S : Finset ℕ) (W R z Q : ℕ) (X L rho C D : ℝ)
    (hne : S.Nonempty) (hWodd : W % 2 = 1)
    (hR : 0 < R) (heven : 2 ∣ R) (hzQ : 0 < z * Q)
    (hX : 0 < X) (hL : 0 < L) (hbefore : (R : ℝ) ≤ X / L)
    (hS : ∀ p ∈ S, (p : ℝ) ≤ X ∧ p % 2 = 1 ∧ Nat.Coprime p W)
    (hrho : 0 < rho) (hdisc : FWAffineWheelDiscrepancy W rho C)
    (hD : 0 < D)
    (hgate : ((z * Q : ℕ) : ℝ) * R ≤
      (1 / (2 * (1 + 1 / L)) : ℝ) * (S.card : ℝ)^2 * R / X -
        (S.card : ℝ) / 2 - (S.card : ℝ) * (rho * D / 2 + C)) :
    let P := sameClassPairs S (progressionBinKey 0 R 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ D ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  classical
  dsimp only
  let P := sameClassPairs S (progressionBinKey 0 R 2)
  obtain ⟨hP, hpairs⟩ := fw_wheel_binned_pairs S X L R hX hL hR hbefore
    (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)
  let short := P.filter fun x => ((x.2 - x.1 : ℕ) : ℝ) < D
  let long := P.filter fun x => D ≤ ((x.2 - x.1 : ℕ) : ℝ)
  have hshort := fw_affine_short_pair_count S P W D rho C hne hWodd
    (fun p hp => ⟨(hS p hp).2.1, (hS p hp).2.2⟩)
    (fun x hx => ⟨(hP x hx).1, (hP x hx).2.1, (hP x hx).2.2.1, (hP x hx).2.2.2.1⟩)
    hD hrho hdisc
  change (short.card : ℝ) < (S.card : ℝ) * (rho * D / 2 + C) at hshort
  have hpart : short.card + long.card = P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := P)
      (fun x => ((x.2 - x.1 : ℕ) : ℝ) < D)
    simpa [short, long, not_lt] using h
  have hpartR : (short.card : ℝ) + long.card = P.card := by exact_mod_cast hpart
  change (1 / (2 * (1 + 1 / L)) : ℝ) * (S.card : ℝ)^2 * R / X -
    (S.card : ℝ) / 2 ≤ (P.card : ℝ) at hpairs
  have hlong : ((z * Q : ℕ) : ℝ) * R < (long.card : ℝ) := by linarith
  have hreal : ((((R / 2) * (2 * (z * Q)) : ℕ) : ℝ)) ≤ ((z * Q : ℕ) : ℝ) * R := by
    have hdiv : (R / 2) * 2 = R := Nat.div_mul_cancel heven
    have hn : (R / 2) * (2 * (z * Q)) = (z * Q) * R := by
      calc
        _ = ((R / 2) * 2) * (z * Q) := by ac_rfl
        _ = (z * Q) * R := by rw [hdiv]; ac_rfl
    exact_mod_cast (le_of_eq hn)
  have hcount : (R / 2) * (2 * (z * Q)) ≤ long.card := by
    exact_mod_cast (hreal.trans (le_of_lt hlong))
  have hvalid : ∀ x ∈ long, x.1 < x.2 ∧ 2 ∣ x.2 - x.1 ∧
      x.2 - x.1 ≤ R ∧ D ≤ ((x.2 - x.1 : ℕ) : ℝ) := by
    intro x hx
    have hp := (Finset.mem_filter.mp hx).1
    have hs := hP x hp
    refine ⟨hs.2.2.1, ?_, hs.2.2.2.2, (Finset.mem_filter.mp hx).2⟩
    omega
  obtain ⟨gap, chosen, hgap, hdiv, hmax, hlow, hcard, hmem, hmatching⟩ :=
    fw_weak_common_gap_matching_from_pairs long 2 R (z * Q) D (by decide) (by omega) hzQ hvalid hcount
  refine ⟨gap, chosen, hgap, hdiv, hlow, hmax, hcard, ?_, ?_, hmatching⟩
  · intro p hp
    exact (Finset.mem_filter.mp (hmem p hp)).1
  · intro p hp
    have hp' := (Finset.mem_filter.mp (hmem p hp)).1
    exact ⟨(hP (p, p + gap) hp').1, (hP (p, p + gap) hp').2.1⟩

end
end Sude
