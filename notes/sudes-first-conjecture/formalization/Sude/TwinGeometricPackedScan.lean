import Sude.TwinGeometricScan
import Sude.TwinPackedCounting

/-! Alternative geometric sieve using the kernel-verified packed byte count.
This module does not change certificate generation or assert a speedup. -/
namespace Sude
noncomputable section

/-- Geometric active-base scan with byte-chunked adjacent-clear population
count and the original one-candidate lookahead. -/
def geometricPackedTwinScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      twinByteChunkedPopCount
        (twinClearMask (geometricSegmentMarkBits
          (activeMarkingBase base lo (width + 1)) lo (width + 1)) width) width +
      geometricPackedTwinScan base (lo + 2 * width) widths

/-- The packed scan equals the geometric stream scan for arbitrary base,
start and segment plan, including zero-width and empty plans. -/
theorem geometricPackedTwinScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    geometricPackedTwinScan base lo widths = geometricActiveStreamingTwinScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [geometricPackedTwinScan, geometricActiveStreamingTwinScan,
      twin_byte_chunked_clear_count_correct, ih]

/-- All-input equality to the exact underlying finite bitset count. -/
theorem geometricPackedTwinScan_eq_bitset (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    geometricPackedTwinScan base lo widths = twinBitsetCountScan base lo widths := by
  rw [geometricPackedTwinScan_eq, geometricActiveStreamingTwinScan_eq,
    activeStreamingTwinScan_eq, streamingTwinScan_eq]

/-- Under the same complete-base and range hypotheses as the original sieve,
the packed scan counts the exact half-open twin-prime lower-endpoint set. -/
theorem geometricPackedTwinScan_spec (base : List ℕ) (bound lo : ℕ)
    (widths : List ℕ) (hbase : CompletePrimeBase base.toFinset bound)
    (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * (widths.sum + 1) ≤ (bound + 1) * (bound + 1)) :
    geometricPackedTwinScan base lo widths =
      (twinPrimeSegment lo (lo + 2 * widths.sum)).card := by
  rw [geometricPackedTwinScan_eq]
  exact geometricActiveStreamingTwinScan_spec base bound lo widths hbase hlo hodd hbound

end
end Sude
