import Sude.PrefixThetaCount

/-! All five source FPF endpoint ranges fit in the exact prescribed pool. -/
namespace Sude
noncomputable section

inductive FPFProfile where
  | low | c27 | medium | high | top
  deriving DecidableEq, Repr

def FPFProfile.minOrder : FPFProfile → ℕ
  | .low => 2000
  | .c27 => 2400
  | .medium => 3000
  | .high => 5000
  | .top => 10000

def FPFProfile.maxOrder : FPFProfile → ℕ
  | .low => 2400
  | .c27 => 3000
  | .medium => 5000
  | .high => 10000
  | .top => 19483

/-- Actual retained endpoint upper bounds from FPF1; C27's sieve bound
is larger than the endpoint interval and is not substituted here. -/
def FPFProfile.endpointUpper : FPFProfile → ℕ
  | .low => 55000000
  | .c27 => 74000000
  | .medium => 150000000
  | .high => 450000000
  | .top => 1800000000

/-- The five inclusive source profile ranges cover the lower-controller
domain, including all overlaps and integer boundary cases. -/
theorem fpf_profile_cover {n : ℕ} (hlo : 2000 ≤ n) (hhi : n ≤ 19483) :
    ∃ f : FPFProfile, f.minOrder ≤ n ∧ n ≤ f.maxOrder := by
  by_cases hL : n ≤ 2400
  · exact ⟨.low, hlo, hL⟩
  · by_cases hC : n ≤ 3000
    · exact ⟨.c27, by dsimp [FPFProfile.minOrder]; omega, hC⟩
    · by_cases hM : n ≤ 5000
      · exact ⟨.medium, by dsimp [FPFProfile.minOrder]; omega, hM⟩
      · by_cases hH : n ≤ 10000
        · exact ⟨.high, by dsimp [FPFProfile.minOrder]; omega, hH⟩
        · exact ⟨.top, by dsimp [FPFProfile.minOrder]; omega, hhi⟩

/-- For any source profile, every odd prime in its actual endpoint range
belongs to the prescribed pool at every order in that profile's domain. -/
theorem fpf_profile_prime_in_pool (lower : RSIndexLower) (bmor : BMORFiniteTheta)
    (f : FPFProfile) {n p : ℕ} (hn : f.minOrder ≤ n)
    (hp : Nat.Prime p) (hne : p ≠ 2) (hbound : p ≤ f.endpointUpper) : p ∈ pool n := by
  cases f with
  | low =>
    apply finitePrefix_L_prime_in_pool lower hn hp hne
    dsimp [FPFProfile.endpointUpper] at hbound
    omega
  | c27 => exact finitePrefix_C27_prime_in_pool lower hn hp hne hbound
  | medium => exact finitePrefix_M_prime_in_pool lower bmor hn hp hne hbound
  | high => exact finitePrefix_H_prime_in_pool lower bmor hn hp hne hbound
  | top => exact finitePrefix_T_prime_in_pool lower hn hp hne hbound

end
end Sude
