import Sude.BMORMatchedBins

/-! Exact modulus-two prime-bin inputs for the matched-block construction. -/
namespace Sude
noncomputable section

/-- Low FW-style bins, as actual primes in half-open intervals. -/
def bmorLowBins {N : ℕ} (b c : Fin N × Bool → ℝ) (i : Fin N) : Finset ℕ :=
  apInterval (b (i, false)) (c (i, false)) 2 1

/-- High FW-style bins, as actual primes in half-open intervals. -/
def bmorHighBins {N : ℕ} (b c : Fin N × Bool → ℝ) (i : Fin N) : Finset ℕ :=
  apInterval (b (i, true)) (c (i, true)) 2 1

/-- Translate published BMOR and explicit interval hypotheses to all stock,
pool, ordering, and gap-label premises of the matched-bin block theorem.
The exact endpoint and numerical gate obligations are still hypotheses. -/
theorem bmor_two_matched_bin_inputs {N : ℕ}
    (h : BMORFiniteTheta) (upper : RSIndexUpper) (n W : ℕ) (b c : Fin N × Bool → ℝ)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (hb : ∀ z, 1 ≤ b z) (hbc : ∀ z, b z ≤ c z)
    (hcX : ∀ z, c z ≤ (poolMaximum n : ℝ))
    (hsep : ∀ z t, z ≠ t → c z ≤ b t ∨ c t ≤ b z)
    (hcross : ∀ i j, c (i, false) ≤ b (j, true))
    (hW : ∀ z, (W : ℝ) ≤
      ((c z - b z) - (518 / 125 : ℝ) * (Real.sqrt (b z) + Real.sqrt (c z))) /
        Real.log (poolMaximum n : ℝ)) :
    let low := bmorLowBins b c
    let high := bmorHighBins b c
    (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun z => if z.2 then high z.1 else low z.1) ∧
    (∀ i, W ≤ (low i).card) ∧ (∀ i, W ≤ (high i).card) ∧
    (∀ i j a, a ∈ low i → ∀ d, d ∈ high j → a < d) ∧
    (∀ i a, a ∈ low i → ∀ d, d ∈ high i → d - a ∈ Finset.range (poolMaximum n)) ∧
    (∀ i p, p ∈ low i → p ∈ pool n) ∧ (∀ i p, p ∈ high i → p ∈ pool n) := by
  classical
  dsimp only
  have hs := bmor_two_separated_bin_supplies h upper n W b c hn hnmax hb hbc hcX hsep hW
  have hbool : (fun z : Fin N × Bool => if z.2 then bmorHighBins b c z.1 else bmorLowBins b c z.1) =
      (fun z => apInterval (b z) (c z) 2 1) := by
    funext z
    rcases z with ⟨i, side⟩
    cases side <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbool]
    exact hs.1
  · intro i
    exact hs.2.1 (i, false)
  · intro i
    exact hs.2.1 (i, true)
  · intro i j a ha d hd
    have ha' := (mem_apInterval_iff _ _ 2 1 (by linarith [hb (i, false)])
      (by linarith [hb (i, false), hbc (i, false)]) a).mp ha
    have hd' := (mem_apInterval_iff _ _ 2 1 (by linarith [hb (j, true)])
      (by linarith [hb (j, true), hbc (j, true)]) d).mp hd
    have hreal : (a : ℝ) < d := lt_of_le_of_lt (ha'.2.2.1.trans (hcross i j)) hd'.2.1
    exact_mod_cast hreal
  · intro i a ha d hd
    have ha' := (mem_apInterval_iff _ _ 2 1 (by linarith [hb (i, false)])
      (by linarith [hb (i, false), hbc (i, false)]) a).mp ha
    have hd' := (mem_apInterval_iff _ _ 2 1 (by linarith [hb (i, true)])
      (by linarith [hb (i, true), hbc (i, true)]) d).mp hd
    have hdpool : d ∈ pool n := hs.2.2 (i, true) d hd
    have hmax := pool_le_poolMaximum hdpool
    have hapos := ha'.1.pos
    have hdpos := hd'.1.pos
    simp only [Finset.mem_range]
    omega
  · intro i p hp
    exact hs.2.2 (i, false) p hp
  · intro i p hp
    exact hs.2.2 (i, true) p hp

end
end Sude
