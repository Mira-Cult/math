import Sude.SegmentedScan
import Mathlib.Data.Nat.Bitwise

/-! A compact natural-number bitset for marking segment candidates. All
correctness claims reduce to the previously verified finite-set sieve. -/
namespace Sude
noncomputable section

/-- Set each listed bit; duplicates are harmless. -/
def encodeMarkBits : List ℕ → ℕ
  | [] => 0
  | i :: rest => (2 ^ i) ||| encodeMarkBits rest

/-- Each bit is set exactly when its index occurs in the list. -/
theorem encodeMarkBits_spec (indices : List ℕ) (i : ℕ) :
    (encodeMarkBits indices).testBit i = decide (i ∈ indices) := by
  induction indices with
  | nil => simp [encodeMarkBits]
  | cons j rest ih =>
    simp [encodeMarkBits, Nat.testBit_two_pow, ih, eq_comm]

/-- A fully reducible list of all base primes, in increasing order. -/
def canonicalPrimeBaseList (bound : ℕ) : List ℕ :=
  (List.range (bound + 1)).filter fun p => decide (Nat.Prime p)

theorem canonicalPrimeBaseList_complete (bound : ℕ) :
    CompletePrimeBase (canonicalPrimeBaseList bound).toFinset bound := by
  intro p
  simp [canonicalPrimeBaseList, and_comm]

/-- Enumerate the marks by their proved arithmetic progressions, without
constructing the finite-set union or testing nonmultiples. -/
def markingIndexList (base : List ℕ) (lo width : ℕ) : List ℕ :=
  (base.filter fun p => p % 2 = 1).flatMap fun p =>
    (List.range (markingCount p lo width)).map (fun t => firstMarkIndex p lo + p * t)

def segmentMarkBits (base : List ℕ) (lo width : ℕ) : ℕ :=
  encodeMarkBits (markingIndexList base lo width)

/-- The encoded progression list represents exactly the earlier proved
finite set of composite indices. -/
theorem markingIndexList_spec (base : List ℕ) (lo width i : ℕ) :
    i ∈ markingIndexList base lo width ↔ i ∈ compositeMarkIndices base.toFinset lo width := by
  simp only [markingIndexList, List.mem_flatMap, List.mem_filter, List.mem_map,
    List.mem_range, compositeMarkIndices, Finset.mem_biUnion, Finset.mem_filter, markingIndices, Finset.mem_image,
    Finset.mem_range, List.mem_toFinset, decide_eq_true_eq]

theorem segmentMarkBits_spec (base : List ℕ) (lo width i : ℕ) :
    (segmentMarkBits base lo width).testBit i = true ↔
      i ∈ compositeMarkIndices base.toFinset lo width := by
  rw [segmentMarkBits, encodeMarkBits_spec]
  simp [markingIndexList_spec]

/-- The unmarked indices extracted from the bitset. -/
def bitsetUnmarked (base : List ℕ) (lo width : ℕ) : Finset ℕ :=
  (Finset.range width).filter fun i => (segmentMarkBits base lo width).testBit i = false

/-- Bitset extraction is extensionally equal to the prior finite-set sieve,
including repeated marks and all out-of-range indices. -/
theorem bitsetUnmarked_eq (base : List ℕ) (lo width : ℕ) :
    bitsetUnmarked base lo width = unmarkedIndices base.toFinset lo width := by
  ext i
  simp only [bitsetUnmarked, Finset.mem_filter, Finset.mem_range, unmarkedIndices,
    Finset.mem_sdiff]
  rw [← segmentMarkBits_spec]
  simp

/-- Compute the count and sum from the compact marked bitset. -/
def bitsetSegmentSummary (base : List ℕ) (lo width : ℕ) : ℕ × ℕ :=
  ((bitsetUnmarked base lo width).card,
    (∑ i ∈ bitsetUnmarked base lo width, (lo + 2 * i)))

theorem bitsetSegmentSummary_eq (base : List ℕ) (lo width : ℕ) :
    bitsetSegmentSummary base lo width = markingSegmentSummary base.toFinset lo width := by
  simp only [bitsetSegmentSummary, markingSegmentSummary, bitsetUnmarked_eq]

/-- The bitset summary is the exact mathematical prime count and sum. -/
theorem bitsetSegmentSummary_spec (base : List ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * width ≤ (bound + 1) * (bound + 1)) :
    bitsetSegmentSummary base lo width =
      ((oddPrimeSegment lo (lo + 2 * width)).card,
        ∑ p ∈ oddPrimeSegment lo (lo + 2 * width), p) := by
  rw [bitsetSegmentSummary_eq]
  exact markingSegmentSummary_spec base.toFinset bound lo width hbase hlo hodd hbound

/-- Scan a finite sequence of segments using compact bitsets. -/
def bitsetSegmentScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | width :: widths =>
    let here := bitsetSegmentSummary base lo width
    let rest := bitsetSegmentScan base (lo + 2 * width) widths
    (here.1 + rest.1, here.2 + rest.2)

/-- Bitset scans and the proved finite-set scans agree for every plan. -/
theorem bitsetSegmentScan_eq (base : List ℕ) (lo : ℕ) (widths : List ℕ) :
    bitsetSegmentScan base lo widths = markingSegmentScan base.toFinset lo widths := by
  induction widths generalizing lo with
  | nil => rfl
  | cons width widths ih =>
    simp only [bitsetSegmentScan, markingSegmentScan, bitsetSegmentSummary_eq, ih]

/-- Independently accepted bitset scans compose at the exact next odd
candidate, without re-evaluating either constituent scan. -/
theorem bitsetSegmentScan_append (base : List ℕ) (lo : ℕ) (xs ys : List ℕ) :
    bitsetSegmentScan base lo (xs ++ ys) =
      ((bitsetSegmentScan base lo xs).1 +
          (bitsetSegmentScan base (lo + 2 * xs.sum) ys).1,
        (bitsetSegmentScan base lo xs).2 +
          (bitsetSegmentScan base (lo + 2 * xs.sum) ys).2) := by
  simp only [bitsetSegmentScan_eq, markingSegmentScan_append]

/-- An accepted bitset scan gives the prescribed pool identities. -/
theorem bitsetScan_pool_identities (base : List ℕ) (bound n X T : ℕ)
    (widths : List ℕ) (hbase : CompletePrimeBase base.toFinset bound) (hX : Nat.Prime X)
    (hX3 : 3 ≤ X) (hodd : X % 2 = 1)
    (hwidth : widths.sum = (X - 3) / 2 + 1)
    (hbound : X + 2 ≤ (bound + 1) * (bound + 1))
    (hscan : bitsetSegmentScan base 3 widths = (n * n, T)) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  rw [bitsetSegmentScan_eq] at hscan
  exact markingSegmentScan_pool_identities base.toFinset bound n X T widths hbase hX hX3 hodd
    hwidth hbound hscan

end
end Sude
