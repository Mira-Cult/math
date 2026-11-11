import Sude.BitsetSieve

/-! One-pass extraction of count and sum from a segment's marking bitset. -/
namespace Sude
noncomputable section

/-- Traverse the bitset from least to most significant, consuming each
candidate exactly once and carrying its corresponding odd value. -/
def streamBitSummary : ℕ → ℕ → ℕ → ℕ × ℕ
  | _, _, 0 => (0, 0)
  | bits, lo, width + 1 =>
      let rest := streamBitSummary (bits / 2) (lo + 2) width
      if bits.testBit 0 then rest else (rest.1 + 1, rest.2 + lo)

/-- The streaming traversal counts and sums precisely the clear bits. -/
theorem streamBitSummary_spec (bits lo width : ℕ) :
    streamBitSummary bits lo width =
      ((∑ i ∈ Finset.range width, if bits.testBit i = false then 1 else 0),
       (∑ i ∈ Finset.range width, if bits.testBit i = false then lo + 2 * i else 0)) := by
  induction width generalizing bits lo with
  | zero => simp [streamBitSummary]
  | succ width ih =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [streamBitSummary, ih, Nat.testBit_succ]
    have hv : ∀ i : ℕ, lo + 2 * (i + 1) = lo + 2 + 2 * i := by intro i; omega
    simp only [hv]
    cases hbit : bits.testBit 0 <;> simp [Nat.add_comm]

/-- One-pass extraction agrees with the prior finite-set calculation. -/
theorem streamBitSummary_eq (bits lo width : ℕ) :
    streamBitSummary bits lo width =
      (((Finset.range width).filter fun i => bits.testBit i = false).card,
       (∑ i ∈ (Finset.range width).filter (fun i => bits.testBit i = false), (lo + 2 * i))) := by
  rw [streamBitSummary_spec, Finset.card_filter, Finset.sum_filter]

/-- Compact marking followed by a single linear traversal of the bitset. -/
def streamingSegmentSummary (base : List ℕ) (lo width : ℕ) : ℕ × ℕ :=
  streamBitSummary (segmentMarkBits base lo width) lo width

theorem streamingSegmentSummary_eq (base : List ℕ) (lo width : ℕ) :
    streamingSegmentSummary base lo width = bitsetSegmentSummary base lo width := by
  simp only [streamingSegmentSummary, bitsetSegmentSummary, bitsetUnmarked, streamBitSummary_eq]

def streamingSegmentScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | width :: widths =>
    let here := streamingSegmentSummary base lo width
    let rest := streamingSegmentScan base (lo + 2 * width) widths
    (here.1 + rest.1, here.2 + rest.2)

/-- The faster traversal preserves the entire scan's exact semantics. -/
theorem streamingSegmentScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    streamingSegmentScan base lo widths = bitsetSegmentScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [streamingSegmentScan, bitsetSegmentScan, streamingSegmentSummary_eq, ih]

/-- Any kernel-accepted streaming scan proves the prescribed pool identities. -/
theorem streamingScan_pool_identities (base : List ℕ) (bound n X T : ℕ)
    (widths : List ℕ) (hbase : CompletePrimeBase base.toFinset bound) (hX : Nat.Prime X)
    (hX3 : 3 ≤ X) (hodd : X % 2 = 1)
    (hwidth : widths.sum = (X - 3) / 2 + 1)
    (hbound : X + 2 ≤ (bound + 1) * (bound + 1))
    (hscan : streamingSegmentScan base 3 widths = (n * n, T)) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  rw [streamingSegmentScan_eq] at hscan
  exact bitsetScan_pool_identities base bound n X T widths hbase hX hX3 hodd hwidth hbound hscan

end
end Sude
