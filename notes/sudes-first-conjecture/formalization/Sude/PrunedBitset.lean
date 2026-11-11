import Sude.StreamingBitset

/-! Prune base entries that cannot mark any candidate in an odd segment.
This is a proved optimization of the sieve, not an acceptance certificate. -/
namespace Sude
noncomputable section

/-- Only entries with square below the segment's exclusive upper bound
can contribute a mark. The list order and multiplicities are retained. -/
def relevantMarkingBase (base : List ℕ) (lo width : ℕ) : List ℕ :=
  base.filter fun p => p * p < lo + 2 * width

theorem relevantMarkingBase_bits_eq (base : List ℕ) (lo width : ℕ)
    (hodd : lo % 2 = 1) :
    segmentMarkBits (relevantMarkingBase base lo width) lo width =
      segmentMarkBits base lo width := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [segmentMarkBits_spec, segmentMarkBits_spec]
  simp only [compositeMarkIndices, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset, relevantMarkingBase, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp, _⟩, hpo⟩, hi⟩
    exact ⟨p, ⟨hp, hpo⟩, hi⟩
  · rintro ⟨p, ⟨hp, hpo⟩, hi⟩
    have hp0 : 0 < p := by omega
    have hspec := (markingIndices_spec p lo width i hp0 hpo hodd).mp hi
    refine ⟨p, ⟨⟨hp, ?_⟩, hpo⟩, hi⟩
    omega

/-- The pruned implementation scans exactly the same finite segment. -/
def prunedSegmentSummary (base : List ℕ) (lo width : ℕ) : ℕ × ℕ :=
  streamingSegmentSummary (relevantMarkingBase base lo width) lo width

theorem prunedSegmentSummary_eq (base : List ℕ) (lo width : ℕ)
    (hodd : lo % 2 = 1) :
    prunedSegmentSummary base lo width = streamingSegmentSummary base lo width := by
  simp only [prunedSegmentSummary, streamingSegmentSummary,
    relevantMarkingBase_bits_eq base lo width hodd]

def prunedSegmentScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | width :: widths =>
    let here := prunedSegmentSummary base lo width
    let rest := prunedSegmentScan base (lo + 2 * width) widths
    (here.1 + rest.1, here.2 + rest.2)

/-- Pruning commutes with every finite scan from an odd initial point. -/
theorem prunedSegmentScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ)
    (hodd : lo % 2 = 1) :
    prunedSegmentScan base lo widths = streamingSegmentScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    have hnext : (lo + 2 * width) % 2 = 1 := by omega
    simp only [prunedSegmentScan, streamingSegmentScan,
      prunedSegmentSummary_eq base lo width hodd, ih _ hnext]

end
end Sude
