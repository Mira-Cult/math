import Sude.TwinSegmentScan

/-! Streaming adjacent clear-bit counts with one-candidate lookahead. -/
namespace Sude
noncomputable section

/-- Traverse adjacent bits without constructing a finite set of pairs. -/
def streamTwinCount : ℕ → ℕ → ℕ
  | _, 0 => 0
  | bits, width + 1 =>
      let rest := streamTwinCount (bits / 2) width
      if bits.testBit 0 = false ∧ bits.testBit 1 = false then rest + 1 else rest

/-- The stream counts each adjacent pair of clear bits exactly once. -/
theorem streamTwinCount_spec (bits width : ℕ) :
    streamTwinCount bits width =
      ∑ i ∈ Finset.range width,
        if bits.testBit i = false ∧ bits.testBit (i + 1) = false then 1 else 0 := by
  induction width generalizing bits with
  | zero => simp [streamTwinCount]
  | succ width ih =>
    rw [Finset.sum_range_succ']
    simp only [streamTwinCount, ih, Nat.testBit_succ]
    split_ifs <;> simp_all [Nat.add_comm]

/-- The stream agrees with the finite-set lookahead checker. -/
theorem streamTwinCount_eq (base : List ℕ) (lo width : ℕ) :
    streamTwinCount (segmentMarkBits base lo (width + 1)) width =
      (twinBitsetLowers base lo width).card := by
  rw [streamTwinCount_spec]
  have hinj : Function.Injective (fun i : ℕ => lo + 2 * i) := by
    intro i j hij
    dsimp only at hij
    omega
  rw [twinBitsetLowers, Finset.card_image_of_injective _ hinj, twinBitsetIndices, Finset.card_filter]

/-- Streaming implementation for the entire explicit segment plan. -/
def streamingTwinScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      streamTwinCount (segmentMarkBits base lo (width + 1)) width +
        streamingTwinScan base (lo + 2 * width) widths

theorem streamingTwinScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    streamingTwinScan base lo widths = twinBitsetCountScan base lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [streamingTwinScan, twinBitsetCountScan, streamTwinCount_eq, ih]

end
end Sude
