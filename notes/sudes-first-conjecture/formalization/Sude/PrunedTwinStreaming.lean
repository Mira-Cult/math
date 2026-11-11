import Sude.TwinStreaming
import Sude.PrunedBitset

/-! Pruned streaming twin-prime scans and independent segment composition. -/
namespace Sude
noncomputable section

/-- Candidate base primes too large to mark the lookahead segment can be
removed without changing the streamed pair count. -/
theorem prunedStreamTwinCount_eq (base : List ℕ) (lo width : ℕ) (hodd : lo % 2 = 1) :
    streamTwinCount (segmentMarkBits (relevantMarkingBase base lo (width + 1)) lo (width + 1)) width =
      streamTwinCount (segmentMarkBits base lo (width + 1)) width := by
  rw [relevantMarkingBase_bits_eq base lo (width + 1) hodd]

def prunedStreamingTwinScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      streamTwinCount (segmentMarkBits (relevantMarkingBase base lo (width + 1)) lo (width + 1)) width +
        prunedStreamingTwinScan base (lo + 2 * width) widths

/-- Pruning preserves every finite scan from an odd starting point. -/
theorem prunedStreamingTwinScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ)
    (hodd : lo % 2 = 1) :
    prunedStreamingTwinScan base lo widths = streamingTwinScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    have hnext : (lo + 2 * width) % 2 = 1 := by omega
    simp only [prunedStreamingTwinScan, streamingTwinScan,
      prunedStreamTwinCount_eq base lo width hodd, ih _ hnext]

/-- Independent streamed segments compose at the exact next lower endpoint. -/
theorem streamingTwinScan_append (base : List ℕ) (lo : ℕ) (xs ys : List ℕ) :
    streamingTwinScan base lo (xs ++ ys) =
      streamingTwinScan base lo xs + streamingTwinScan base (lo + 2 * xs.sum) ys := by
  simp only [streamingTwinScan_eq, twinBitsetCountScan_append]

end
end Sude
