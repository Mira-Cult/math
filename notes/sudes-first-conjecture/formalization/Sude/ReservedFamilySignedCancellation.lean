import Sude.ReservedPoolSignedMean
import Sude.SignedPoolMeanCancellation

/-! Signed cancellation for a supplied physical reservation partition.
This does not establish the reservation counts, family deviation, or any
completion, line estimate, or prime target. -/
namespace Sude
noncomputable section

/-- Combine an actual reserved-cell partition with the signed pool-mean
update. The remainder's signed deviation is retained explicitly. -/
theorem actual_reserved_family_signed_cancellation {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved family : Finset (Cell n))
    (d r q br familyCount : ℕ) (A : ℝ)
    (hsub : family ⊆ reserved)
    (hfamilyCard : family.card = familyCount)
    (hreservedCard : reserved.card = r * (n + 8) + br)
    (hreserved : reserved.card < n * n) (hline : r + q ≤ n)
    (hfamilyDeviation :
      (∑ z ∈ family, (entry a z : ℝ)) -
          (familyCount : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue =
        2 * (d : ℝ) * ((n : ℝ) + 8) * A) :
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let other : ℝ := (∑ z ∈ reserved \ family, (entry a z : ℝ)) -
      ((reserved \ family).card : ℝ) * μ
    let N : ℝ := (n * n - (r * (n + 8) + br) : ℕ)
    let k : ℝ := (n - r - q : ℕ)
    2 * (d : ℝ) * A + k *
        (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - μ) =
      (2 * (d : ℝ) * A / N) * (((n : ℝ) + 8) * (q : ℝ) - br - 8 * n) -
        k * other / N := by
  classical
  dsimp only
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let other : ℝ := (∑ z ∈ reserved \ family, (entry a z : ℝ)) -
    ((reserved \ family).card : ℝ) * μ
  have hcount : r * (n + 8) + br < n * n := by simpa [hreservedCard] using hreserved
  have hsum := Finset.sum_sdiff (f := fun z => (entry a z : ℝ)) hsub
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hcardR : (((reserved \ family).card : ℕ) : ℝ) + (family.card : ℝ) = reserved.card := by
    exact_mod_cast hcard
  have hdev : (∑ z ∈ reserved, (entry a z : ℝ)) - (reserved.card : ℝ) * μ =
      2 * (d : ℝ) * ((n : ℝ) + 8) * A + other := by
    rw [hfamilyCard] at hcardR
    have hc := congrArg (fun x : ℝ => x * μ) hcardR
    change (∑ z ∈ family, (entry a z : ℝ)) - (familyCount : ℝ) * μ = _ at hfamilyDeviation
    dsimp [other]
    linarith [hsum, hc, hfamilyDeviation]
  have hpos : 0 < (actualUnusedPool a reserved).card := by
    rw [actualUnusedPool_card_eq_sub]
    omega
  have hmean := actual_unused_mean_signed_update a reserved hpos
  have hN : ((actualUnusedPool a reserved).card : ℝ) =
      ((n * n - (r * (n + 8) + br) : ℕ) : ℝ) := by
    rw [actualUnusedPool_card_eq_sub, hreservedCard]
  rw [hN, hdev] at hmean
  have hscalar := signed_family_unused_mean_cancellation n d r q br A other hcount hline
  dsimp only at hscalar
  change centralEntriesMean (actualUnusedPool a reserved) centralPoolValue = μ - _ at hmean
  rw [hmean]
  convert hscalar using 1 <;> ring

end
end Sude
