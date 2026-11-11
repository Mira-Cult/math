import Sude.TwinStreaming

/-! Remove base entries whose first marking position is outside a segment. -/
namespace Sude
noncomputable section

/-- A base entry is active exactly when its first mark is in the segment. -/
def activeMarkingBase (base : List ℕ) (lo width : ℕ) : List ℕ :=
  base.filter fun p => firstMarkIndex p lo < width

/-- Removing inactive entries leaves every bit unchanged. This uses the
proved marking progression and does not assume the entries are prime. -/
theorem activeMarkingBase_bits_eq (base : List ℕ) (lo width : ℕ) :
    segmentMarkBits (activeMarkingBase base lo width) lo width = segmentMarkBits base lo width := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [segmentMarkBits_spec, segmentMarkBits_spec]
  simp only [compositeMarkIndices, Finset.mem_biUnion, Finset.mem_filter,
    List.mem_toFinset, activeMarkingBase, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp, _⟩, hpodd⟩, hi⟩
    exact ⟨p, ⟨hp, hpodd⟩, hi⟩
  · rintro ⟨p, ⟨hp, hpodd⟩, hi⟩
    have hfirst : firstMarkIndex p lo < width := by
      obtain ⟨t, ht, _⟩ := Finset.mem_image.mp hi
      have ht' := Finset.mem_range.mp ht
      unfold markingCount at ht'
      split_ifs at ht' with h
      · exact h
      · omega
    exact ⟨p, ⟨⟨hp, hfirst⟩, hpodd⟩, hi⟩

/-- The exact same twin-pair count results after active-base pruning. -/
theorem activeStreamTwinCount_eq (base : List ℕ) (lo width : ℕ) :
    streamTwinCount (segmentMarkBits (activeMarkingBase base lo (width + 1)) lo (width + 1)) width =
      streamTwinCount (segmentMarkBits base lo (width + 1)) width := by
  rw [activeMarkingBase_bits_eq]

/-- Stream the entire plan after discarding inactive base entries separately
for each lookahead segment. -/
def activeStreamingTwinScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      streamTwinCount (segmentMarkBits (activeMarkingBase base lo (width + 1)) lo (width + 1)) width +
        activeStreamingTwinScan base (lo + 2 * width) widths

/-- Active pruning preserves every finite scan, including segment crossings. -/
theorem activeStreamingTwinScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    activeStreamingTwinScan base lo widths = streamingTwinScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [activeStreamingTwinScan, streamingTwinScan,
      activeStreamTwinCount_eq, ih]

end
end Sude
