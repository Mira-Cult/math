import Sude.ActiveTwinBase
import Sude.TwinProgressionMask

/-! An alternative finite twin scan using the proved geometric progression
masks. Its results have exactly the same mathematical specification as the
existing active-base scanner; performance is a separate empirical question. -/
namespace Sude
noncomputable section

/-- Scan with the same active-base pruning and one-candidate lookahead as
`activeStreamingTwinScan`, replacing individual marking bits with their
proved geometric mask. -/
def geometricActiveStreamingTwinScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      streamTwinCount (geometricSegmentMarkBits
        (activeMarkingBase base lo (width + 1)) lo (width + 1)) width +
      geometricActiveStreamingTwinScan base (lo + 2 * width) widths

/-- The alternate scanner equals the original for any base and plan,
including empty and zero-width segments. -/
theorem geometricActiveStreamingTwinScan_eq (base : List ℕ) (lo : ℕ)
    (widths : List ℕ) :
    geometricActiveStreamingTwinScan base lo widths =
      activeStreamingTwinScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [geometricActiveStreamingTwinScan, activeStreamingTwinScan,
      geometricSegmentMarkBits_eq, ih]

/-- The alternate scanner counts exactly the mathematical twin-prime lower
endpoints in the combined half-open interval under the original complete-base
and range hypotheses. -/
theorem geometricActiveStreamingTwinScan_spec (base : List ℕ) (bound lo : ℕ)
    (widths : List ℕ) (hbase : CompletePrimeBase base.toFinset bound)
    (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * (widths.sum + 1) ≤ (bound + 1) * (bound + 1)) :
    geometricActiveStreamingTwinScan base lo widths =
      (twinPrimeSegment lo (lo + 2 * widths.sum)).card := by
  rw [geometricActiveStreamingTwinScan_eq, activeStreamingTwinScan_eq, streamingTwinScan_eq]
  exact twinBitsetCountScan_spec base bound lo widths hbase hlo hodd hbound

end
end Sude
