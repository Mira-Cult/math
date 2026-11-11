import Sude.FWAffineWheelNeighbors

/-! Exact interval accounting for AW1. No wheel-discrepancy estimate is
asserted here. See `problems/prime-line-sums/manuscripts/
cutoff2_affine_wheel_prefix.md`, AW1. -/
namespace Sude
noncomputable section

/-- W-units in the K consecutive positive positions after a. -/
def fwIntervalUnits (W a K : ℕ) : Finset ℕ :=
  (Finset.Ioc a (a + K)).filter (fun x => Nat.Coprime x W)

/-- Multiples of p among W-units correspond, by division by p, to an
interval of W-units of the exact quotient length. -/
theorem fw_interval_units_multiples_card
    (W p a K : ℕ) (hp : Nat.Prime p) (hcop : Nat.Coprime p W) :
    ((fwIntervalUnits W a K).filter (fun x => p ∣ x)).card =
      (fwIntervalUnits W (a / p) ((a + K) / p - a / p)).card := by
  classical
  have hle : a / p ≤ (a + K) / p := Nat.div_le_div_right (by omega)
  have hend : a / p + ((a + K) / p - a / p) = (a + K) / p := Nat.add_sub_of_le hle
  apply Finset.card_bij (fun x _ => x / p)
  · intro x hx
    obtain ⟨hxunit, hdiv⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxrange, hunit⟩ := Finset.mem_filter.mp hxunit
    obtain ⟨hxa, hxend⟩ := Finset.mem_Ioc.mp hxrange
    have heq : x / p * p = x := Nat.div_mul_cancel hdiv
    have hxa' : a / p < x / p := by
      apply (Nat.div_lt_iff_lt_mul hp.pos).2
      omega
    have hxend' : x / p ≤ (a + K) / p := Nat.div_le_div_right hxend
    have hxunit' : Nat.Coprime (x / p) W := by
      have hprod : Nat.Coprime (x / p * p) W := by simpa [heq] using hunit
      exact (Nat.coprime_mul_iff_left.mp hprod).1
    simp only [fwIntervalUnits, Finset.mem_filter, Finset.mem_Ioc, hend]
    exact ⟨⟨hxa', hxend'⟩, hxunit'⟩
  · intro x hx y hy hxy
    change x / p = y / p at hxy
    have hxdiv := (Finset.mem_filter.mp hx).2
    have hydiv := (Finset.mem_filter.mp hy).2
    have hx' := Nat.div_mul_cancel hxdiv
    have hy' := Nat.div_mul_cancel hydiv
    calc
      x = x / p * p := hx'.symm
      _ = y / p * p := by rw [hxy]
      _ = y := hy'
  · intro t ht
    obtain ⟨htrange, htunit⟩ := Finset.mem_filter.mp ht
    obtain ⟨hta, htend⟩ := Finset.mem_Ioc.mp htrange
    rw [hend] at htend
    have hta' : a < t * p := (Nat.div_lt_iff_lt_mul hp.pos).1 hta
    have htend' : t * p ≤ a + K := (Nat.le_div_iff_mul_le hp.pos).1 htend
    have hunit : Nat.Coprime (t * p) W := Nat.coprime_mul_iff_left.mpr ⟨htunit, hcop⟩
    refine ⟨t * p, ?_, ?_⟩
    · simp only [fwIntervalUnits, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨⟨hta', htend'⟩, hunit⟩, dvd_mul_left p t⟩
    · simpa [Nat.mul_comm] using Nat.mul_div_cancel_left t hp.pos

/-- The Wp-units are the W-units left after removing precisely the multiples
of p. This is an exact identity, including empty intervals. -/
theorem fw_interval_units_prime_extension
    (W p a K : ℕ) (hp : Nat.Prime p) (hcop : Nat.Coprime p W) :
    (fwIntervalUnits (W * p) a K).card +
      (fwIntervalUnits W (a / p) ((a + K) / p - a / p)).card =
      (fwIntervalUnits W a K).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := fwIntervalUnits W a K)
    (fun x => p ∣ x)
  have heq : (fwIntervalUnits W a K).filter (fun x => ¬ p ∣ x) =
      fwIntervalUnits (W * p) a K := by
    ext x
    simp only [fwIntervalUnits, Finset.mem_filter, Nat.coprime_mul_iff_right]
    have hprime : Nat.Coprime x p ↔ ¬ p ∣ x := by
      rw [Nat.coprime_comm]
      exact hp.coprime_iff_not_dvd
    rw [hprime]
    tauto
  rw [heq, fw_interval_units_multiples_card W p a K hp hcop] at hsplit
  omega

/-- Every initial translated positive-unit window is the same finite set of
units as the corresponding consecutive interval, up to the shift by a. -/
theorem fw_interval_units_eq_window_card (W a K : ℕ) :
    (fwIntervalUnits W a K).card =
      ((Finset.Icc 1 K).filter (fun j => Nat.Coprime (a + j) W)).card := by
  classical
  apply Finset.card_bij (fun x _ => x - a)
  · intro x hx
    obtain ⟨hmem, hunit⟩ := Finset.mem_filter.mp hx
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hmem
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simpa [Nat.add_sub_of_le (by omega : a ≤ x)] using hunit
  · intro x hx y hy hxy
    have hx' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1).1
    have hy' := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1).1
    change x - a = y - a at hxy
    omega
  · intro j hj
    obtain ⟨hjrange, hunit⟩ := Finset.mem_filter.mp hj
    obtain ⟨hjlo, hjhi⟩ := Finset.mem_Icc.mp hjrange
    refine ⟨a + j, ?_, ?_⟩
    · simp only [fwIntervalUnits, Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨by omega, by omega⟩, hunit⟩
    · simp

/-- An upper bound holding on all consecutive intervals supplies the upper
discrepancy input consumed by the AW2 short-neighbor theorem. -/
theorem fw_interval_upper_implies_affine_discrepancy (W : ℕ) (rho C : ℝ)
    (hupper : ∀ a K : ℕ, ((fwIntervalUnits W a K).card : ℝ) ≤ rho * K + C) :
    FWAffineWheelDiscrepancy W rho C := by
  intro a K _
  simpa [fw_interval_units_eq_window_card] using hupper a K

end
end Sude
