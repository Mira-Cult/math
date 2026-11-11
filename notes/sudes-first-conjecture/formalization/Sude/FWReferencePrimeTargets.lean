import Sude.TargetRouting

/-! Convert explicit prime targets and reference discrepancies into bounded
integer demands for one supplied physical demand-realization interface. -/
namespace Sude
noncomputable section

/-- Given prime odd targets compatible with the pool total and close enough to
this very reference square, any supplied realization of the bounded demand box
produces those row and column targets while preserving its stated reservations
and diagonals. This does not construct targets or prove their discrepancies. -/
theorem fw_reference_prime_targets_of_demands {n B : ℕ} (hn : Odd n)
    (b₀ : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rowTarget colTarget : Fin n → ℕ)
    (hrowPrime : ∀ i, Nat.Prime (rowTarget i))
    (hcolPrime : ∀ i, Nat.Prime (colTarget i))
    (hrowOdd : ∀ i, Odd (rowTarget i))
    (hcolOdd : ∀ i, Odd (colTarget i))
    (hrowTotal : (∑ i, rowTarget i) = Lucas.poolTotal n)
    (hcolTotal : (∑ i, colTarget i) = Lucas.poolTotal n)
    (hrowBound : ∀ i, |(rowTarget i : ℤ) - rowSum b₀ i| ≤ (2 : ℤ) * B)
    (hcolBound : ∀ i, |(colTarget i : ℤ) - columnSum b₀ i| ≤ (2 : ℤ) * B)
    (hrealize : ∀ dr : Fin n → ℤ, (∑ i, dr i = 0) → (∀ i, |dr i| ≤ (B : ℤ)) →
      ∀ dc : Fin n → ℤ, (∑ i, dc i = 0) → (∀ i, |dc i| ≤ (B : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ i, (rowSum b i : ℤ) - rowSum b₀ i = 2 * dr i) ∧
        (∀ i, (columnSum b i : ℤ) - columnSum b₀ i = 2 * dc i) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b)) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ i, rowSum b i = rowTarget i ∧ Nat.Prime (rowSum b i)) ∧
      (∀ i, columnSum b i = colTarget i ∧ Nat.Prime (columnSum b i)) ∧
      mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
      (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  let dr : Fin n → ℤ := fun i => halfLineDemand (rowTarget i) (rowSum b₀ i)
  let dc : Fin n → ℤ := fun i => halfLineDemand (colTarget i) (columnSum b₀ i)
  have hrowSum : (∑ i, rowTarget i) = ∑ i, rowSum b₀ i := by
    rw [hrowTotal, Lucas.sum_rowSums]
  have hcolSum : (∑ i, colTarget i) = ∑ i, columnSum b₀ i := by
    rw [hcolTotal, Lucas.sum_columnSums]
  have ⟨hzr, her⟩ := halfLineDemand_system rowTarget (rowSum b₀) hrowOdd (rowSum_odd hn b₀) hrowSum
  have ⟨hzc, hec⟩ := halfLineDemand_system colTarget (columnSum b₀) hcolOdd (columnSum_odd hn b₀) hcolSum
  have hdr : ∀ i, |dr i| ≤ (B : ℤ) := fun i =>
    halfLineDemand_bound _ _ B (hrowOdd i) (rowSum_odd hn b₀ i) (hrowBound i)
  have hdc : ∀ i, |dc i| ≤ (B : ℤ) := fun i =>
    halfLineDemand_bound _ _ B (hcolOdd i) (columnSum_odd hn b₀ i) (hcolBound i)
  obtain ⟨b, hr, hc, hm, ha, hfixed, hpool, hinj⟩ := hrealize dr hzr hdr dc hzc hdc
  refine ⟨b, ?_, ?_, hm, ha, hfixed, hpool, hinj⟩
  · intro i
    have heq : rowSum b i = rowTarget i := by
      have h₁ := hr i
      have h₂ := her i
      change (rowSum b i : ℤ) - rowSum b₀ i =
        2 * halfLineDemand (rowTarget i) (rowSum b₀ i) at h₁
      exact_mod_cast (show (rowSum b i : ℤ) = rowTarget i by omega)
    exact ⟨heq, heq.symm ▸ hrowPrime i⟩
  · intro i
    have heq : columnSum b i = colTarget i := by
      have h₁ := hc i
      have h₂ := hec i
      change (columnSum b i : ℤ) - columnSum b₀ i =
        2 * halfLineDemand (colTarget i) (columnSum b₀ i) at h₁
      exact_mod_cast (show (columnSum b i : ℤ) = colTarget i by omega)
    exact ⟨heq, heq.symm ▸ hcolPrime i⟩

end
end Sude
