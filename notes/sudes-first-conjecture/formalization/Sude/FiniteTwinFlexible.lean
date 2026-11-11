import Sude.FiniteTwinSeed
import Sude.TwinStreaming

/-! Split the finite FT acceptance obligation into independently checked pieces. -/
namespace Sude
noncomputable section

/-- Any exact partition into odd lower-endpoint widths may be used for FT;
the checker still requires kernel acceptance of the entire scan. -/
theorem finiteTwinSeeds_count_of_partition (base : List ℕ) (widths : List ℕ)
    (hbase : CompletePrimeBase base.toFinset 32768)
    (hwidth : widths.sum = 536870889)
    (hscan : streamingTwinScan base 45 widths = 3650551) :
    finiteTwinSeeds.card = 3650551 := by
  have hbit : twinBitsetCountScan base 45 widths = 3650551 := by
    rw [← streamingTwinScan_eq]
    exact hscan
  have h := twinBitsetCountScan_spec base 32768 45 widths hbase (by decide) (by decide)
    (by rw [hwidth]; decide)
  rw [hbit, hwidth] at h
  have hend : 45 + 2 * 536870889 = 2 ^ 30 - 1 := by decide
  simpa [finiteTwinSeeds, hend] using h.symm

/-- Independently proved adjacent mathematical segment counts combine
without rerunning either scan and without losing boundary pairs. -/
theorem combineTwinPrimeSegments {lo mid hi c₁ c₂ : ℕ} (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (h₁ : (twinPrimeSegment lo mid).card = c₁)
    (h₂ : (twinPrimeSegment mid hi).card = c₂) :
    (twinPrimeSegment lo hi).card = c₁ + c₂ := by
  have h := twinPrimeSegment_union hlm hmh
  rw [← h.2, Finset.card_union_of_disjoint h.1, h₁, h₂]

end
end Sude
