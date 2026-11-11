import Sude.PrefixCount
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Source-Faithful Rosser–Schoenfeld (1962) Prime-Count Imports

Encodes the published explicit `π(x)` bounds from Rosser–Schoenfeld (1962),
*Illinois J. Math.* 6, 64–94, Theorem 2 `(3.3)`–`(3.4)` and Corollary 1 `(3.5)`–`(3.6)`,
printed p. 69. See `import-map.json` for exact source locators and normalizations.
-/

namespace Sude

noncomputable section

set_option autoImplicit false

/-- Number of primes `p ≤ x` for `x ≥ 0`, normalized identically to `π(x)` in
    Rosser–Schoenfeld (1962), equation `(1.1)` / Theorem 2, p. 69. -/
def primeCountReal (x : ℝ) : ℝ :=
  (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ)

theorem primeCountReal_nonneg (x : ℝ) : 0 ≤ primeCountReal x :=
  Nat.cast_nonneg _

theorem primeCountReal_mono {x y : ℝ} (hxy : x ≤ y) :
    primeCountReal x ≤ primeCountReal y := by
  unfold primeCountReal
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter Nat.Prime
    (Finset.range_mono (Nat.succ_le_succ (Nat.floor_mono hxy))))

theorem primeCountReal_natCast_eq_count (B : ℕ) :
    primeCountReal (B : ℝ) = (Nat.count Nat.Prime (B + 1) : ℝ) := by
  unfold primeCountReal
  rw [Nat.floor_natCast, ← Nat.count_eq_card_filter_range]

theorem primeCountReal_natCast_eq_oddPrefix_add_one {B : ℕ} (hB : 2 ≤ B) :
    primeCountReal (B : ℝ) = ((oddPrimePrefix B).card : ℝ) + 1 := by
  rw [primeCountReal_natCast_eq_count, prime_count_succ_eq_oddPrefix_add_one hB]
  push_cast
  ring

theorem oddPrimePrefix_card_le_primeCountReal (B : ℕ) :
    ((oddPrimePrefix B).card : ℝ) ≤ primeCountReal (B : ℝ) := by
  unfold oddPrimePrefix primeCountReal
  rw [Nat.floor_natCast]
  have hsub : (Finset.range (B + 1)).filter (fun p => Nat.Prime p ∧ p ≠ 2) ⊆
      (Finset.range (B + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Rosser–Schoenfeld (1962), Theorem 2, equation `(3.3)`, printed p. 69:
    for every real `x ≥ 67`, `x / (log x - 1/2) < π(x)`. -/
def RSPrimeCountLowerSharp : Prop :=
  ∀ x : ℝ, 67 ≤ x → x / (Real.log x - 1 / 2) < primeCountReal x

/-- Rosser–Schoenfeld (1962), Theorem 2, equation `(3.4)`, printed p. 69:
    for every real `x > exp(3/2)`, `π(x) < x / (log x - 3/2)`. -/
def RSPrimeCountUpperSharp : Prop :=
  ∀ x : ℝ, Real.exp (3 / 2) < x → primeCountReal x < x / (Real.log x - 3 / 2)

/-- Rosser–Schoenfeld (1962), Theorem 2 Corollary 1, equation `(3.5)`, printed p. 69:
    for every real `x ≥ 17`, `x / log x < π(x)`. -/
def RSPrimeCountLower : Prop :=
  ∀ x : ℝ, 17 ≤ x → x / Real.log x < primeCountReal x

/-- Rosser–Schoenfeld (1962), Theorem 2 Corollary 1, equation `(3.6)`, printed p. 69:
    for every real `x > 1`, `π(x) < 1.25506 * x / log x`. -/
def RSPrimeCountUpper : Prop :=
  ∀ x : ℝ, 1 < x → primeCountReal x < (62753 / 50000 : ℝ) * x / Real.log x

/-- Bundled Rosser–Schoenfeld (1962) Theorem 2 and Corollary 1 prime-count hypotheses. -/
structure RSPrimeCountImports : Prop where
  lower_sharp : RSPrimeCountLowerSharp
  upper_sharp : RSPrimeCountUpperSharp
  lower : RSPrimeCountLower
  upper : RSPrimeCountUpper

end

end Sude
