import Sude.FWWheelShortPairs
import Sude.ScreenedPool

/-!
The eight affine-wheel factor lists in the frozen FW mixed recipe extend
[3,5,7,11,13] successively by 17,19,23,29,31,37,41,43. The generic exact
wheel-window bound below is a separate mathematical specialization for
these moduli; the source's eight steps use affine-wheel mode and their
numerical gates are not established here.
-/
namespace Sude
noncomputable section

/-- The eight source affine-wheel prime lists, indexed from zero. -/
def fwMixedWheelFactors (i : Fin 8) : List ℕ :=
  ([3,5,7,11,13,17,19,23,29,31,37,41,43] : List ℕ).take (6 + i.val)

/-- The product of the prime factors of a source affine wheel. -/
def fwMixedWheel (i : Fin 8) : ℕ := (fwMixedWheelFactors i).prod

/-- Every displayed factor is prime and no factor exceeds the screening bound. -/
theorem fw_mixed_wheel_factors (i : Fin 8) :
    ∀ q ∈ fwMixedWheelFactors i, Nat.Prime q ∧ q ≤ 43 := by
  fin_cases i <;> decide

/-- The eight wheel products in source order. -/
theorem fw_mixed_wheel_values :
    List.ofFn fwMixedWheel = [255255, 4849845, 111546435, 3234846615,
      100280245065, 3710369067405, 152125131763605, 6541380665835015] := by
  decide

/-- Every mixed wheel has positive odd modulus. -/
theorem fw_mixed_wheel_pos_odd (i : Fin 8) :
    0 < fwMixedWheel i ∧ fwMixedWheel i % 2 = 1 := by
  fin_cases i <;> norm_num [fwMixedWheel, fwMixedWheelFactors]

/-- Any prime above the screening threshold is a unit for each source wheel. -/
theorem fw_screened_prime_coprime_mixed_wheel (i : Fin 8) (p : ℕ)
    (hp : Nat.Prime p) (hlarge : 43 < p) : Nat.Coprime p (fwMixedWheel i) := by
  exact fw_screened_prime_coprime_wheel (fwMixedWheelFactors i) p hp hlarge
    (fw_mixed_wheel_factors i)

/-- Every surviving value of any screened pool subset is an odd prime and a
unit for every one of the eight affine wheels. -/
theorem fw_screened_pool_mixed_wheel_units {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p)) :
    ∀ p ∈ S, p ∈ pool n ∧ 43 < p ∧ p % 2 = 1 ∧
      ∀ i : Fin 8, Nat.Coprime p (fwMixedWheel i) := by
  intro p hp
  have hp' := Finset.mem_filter.mp (hS hp)
  have hpool := mem_poolFinset.mp hp'.1
  have hprime := pool_prime_and_residue hpool
  exact ⟨hpool, hp'.2, hprime.2, fun i =>
    fw_screened_prime_coprime_mixed_wheel i p hprime.1 hp'.2⟩

/-- The generic exact-wheel all-T unit count holds for any of the eight
source moduli. This does not assert the source affine-mode schedule. -/
theorem fw_mixed_wheel_exact_window (i : Fin 8) (T a : ℕ)
    (ha : Nat.Coprime a (fwMixedWheel i)) :
    ((Finset.Ico 1 (fwWheelWindowCutoff (fwWheelUnit (fwMixedWheel i))
      (fwMixedWheel i) (Nat.totient (fwMixedWheel i)) T
      (Nat.totient_pos.mpr (fw_mixed_wheel_pos_odd i).1))).filter
      (fun j => Nat.Coprime (a+j) (fwMixedWheel i))).card ≤ T :=
  fw_wheel_window_bound_of_pos (fwMixedWheel i) T a (fw_mixed_wheel_pos_odd i).1 ha

/-- For each mixed wheel and each T, the generic exact-window cutoff bounds
short ordered pairs in every screened pool subset. The cutoff condition is
explicit; this does not establish a stage or the affine numerical gates. -/
theorem fw_mixed_wheel_screened_short_pairs (i : Fin 8) {n : ℕ} {S : Finset ℕ}
    (T h : ℕ) (hS : S ⊆ (poolFinset n).filter (fun p => 43 < p))
    (hcut : h ≤ 2 * fwWheelWindowCutoff (fwWheelUnit (fwMixedWheel i))
      (fwMixedWheel i) (Nat.totient (fwMixedWheel i)) T
      (Nat.totient_pos.mpr (fw_mixed_wheel_pos_odd i).1)) :
    (fwWheelShortPairs S h).card ≤ S.card * T := by
  apply fw_wheel_short_pairs_bound S (fwMixedWheel i) T h
    (fw_mixed_wheel_pos_odd i).1 (fw_mixed_wheel_pos_odd i).2 _ hcut
  intro p hp
  have hh := fw_screened_pool_mixed_wheel_units hS p hp
  exact ⟨hh.2.2.1, hh.2.2.2 i⟩

end
end Sude
