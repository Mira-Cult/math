import Sude.BitsetSieve

/-! Parameterized transfer and combination of already accepted scans. -/
namespace Sude
noncomputable section

/-- Convert a checked bitset scan to its mathematical segment count and sum,
while all endpoints remain symbolic. -/
theorem bitsetScan_count_sum (base : List ℕ) (bound lo : ℕ) (widths : List ℕ)
    (count total : ℕ) (hbase : CompletePrimeBase base.toFinset bound)
    (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * widths.sum ≤ (bound + 1) * (bound + 1))
    (hscan : bitsetSegmentScan base lo widths = (count, total)) :
    (oddPrimeSegment lo (lo + 2 * widths.sum)).card = count ∧
      (∑ p ∈ oddPrimeSegment lo (lo + 2 * widths.sum), p) = total := by
  have hs := markingSegmentScan_spec base.toFinset bound lo widths hbase hlo hodd hbound
  have he := bitsetSegmentScan_eq base lo widths
  have hpair : (count, total) =
      ((oddPrimeSegment lo (lo + 2 * widths.sum)).card,
        ∑ p ∈ oddPrimeSegment lo (lo + 2 * widths.sum), p) :=
    hscan.symm.trans (he.trans hs)
  exact ⟨(congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm⟩

/-- Combine two already proved interval results with no recomputation. -/
theorem combineOddPrimeSegments {lo mid hi c₁ c₂ s₁ s₂ : ℕ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (h₁ : (oddPrimeSegment lo mid).card = c₁ ∧
      (∑ p ∈ oddPrimeSegment lo mid, p) = s₁)
    (h₂ : (oddPrimeSegment mid hi).card = c₂ ∧
      (∑ p ∈ oddPrimeSegment mid hi, p) = s₂) :
    (oddPrimeSegment lo hi).card = c₁ + c₂ ∧
      (∑ p ∈ oddPrimeSegment lo hi, p) = s₁ + s₂ := by
  have h := oddPrimeSegment_additive hlm hmh
  exact ⟨h.1.trans (congrArg₂ (· + ·) h₁.1 h₂.1),
    h.2.trans (congrArg₂ (· + ·) h₁.2 h₂.2)⟩

end
end Sude
