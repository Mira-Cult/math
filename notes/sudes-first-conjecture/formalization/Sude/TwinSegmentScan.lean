import Sude.TwinSegmentSieve

/-! Compose gap-two sieve segments without losing boundary-crossing pairs. -/
namespace Sude
noncomputable section

/-- Adjacent half-open lower-endpoint segments are disjoint and cover their
union even if a prime pair crosses the segment boundary. -/
theorem twinPrimeSegment_union {lo mid hi : ℕ} (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    Disjoint (twinPrimeSegment lo mid) (twinPrimeSegment mid hi) ∧
      twinPrimeSegment lo mid ∪ twinPrimeSegment mid hi = twinPrimeSegment lo hi := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp hq
    omega
  · ext p
    simp only [twinPrimeSegment, Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro (⟨⟨hlo, hmid⟩, hp, hp2, hodd⟩ | ⟨⟨hmid, hhi⟩, hp, hp2, hodd⟩)
      · exact ⟨⟨hlo, by omega⟩, hp, hp2, hodd⟩
      · exact ⟨⟨by omega, hhi⟩, hp, hp2, hodd⟩
    · rintro ⟨⟨hlo, hhi⟩, hp, hp2, hodd⟩
      by_cases h : p < mid
      · exact Or.inl ⟨⟨hlo, h⟩, hp, hp2, hodd⟩
      · exact Or.inr ⟨⟨by omega, hhi⟩, hp, hp2, hodd⟩

/-- Count each segment's lower endpoints; lookahead is used independently
for each segment, and the half-open ranges prevent double counting. -/
def twinBitsetCountScan (base : List ℕ) (lo : ℕ) : List ℕ → ℕ
  | [] => 0
  | width :: widths =>
      (twinBitsetLowers base lo width).card +
        twinBitsetCountScan base (lo + 2 * width) widths

/-- Every finite scan is exactly the number of genuine gap-two pairs in its
combined half-open lower-endpoint interval. -/
theorem twinBitsetCountScan_spec (base : List ℕ) (bound lo : ℕ) (widths : List ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * (widths.sum + 1) ≤ (bound + 1) * (bound + 1)) :
    twinBitsetCountScan base lo widths = (twinPrimeSegment lo (lo + 2 * widths.sum)).card := by
  induction widths generalizing lo with
  | nil => simp [twinBitsetCountScan, twinPrimeSegment]
  | cons width widths ih =>
    have hnext : (lo + 2 * width) % 2 = 1 := by omega
    have hlo' : 3 ≤ lo + 2 * width := by omega
    have hbound' : lo + 2 * width + 2 * (widths.sum + 1) ≤ (bound + 1) * (bound + 1) := by
      simp only [List.sum_cons] at hbound
      omega
    have hboundHere : lo + 2 * (width + 1) ≤ (bound + 1) * (bound + 1) := by
      simp only [List.sum_cons] at hbound
      omega
    have hseg := twinBitsetLowers_spec base bound lo width hbase hlo hodd hboundHere
    have htail := ih (lo + 2 * width) hlo' hnext hbound'
    have hpart := twinPrimeSegment_union (lo := lo) (mid := lo + 2 * width)
      (hi := lo + 2 * width + 2 * widths.sum) (by omega) (by omega)
    simp only [twinBitsetCountScan, List.sum_cons]
    rw [hseg, htail, ← Finset.card_union_of_disjoint hpart.1, hpart.2]
    simp only [Nat.mul_add, Nat.add_assoc]

/-- Combine any two independently accepted scans with the exact next odd
lower endpoint. -/
theorem twinBitsetCountScan_append (base : List ℕ) (lo : ℕ) (xs ys : List ℕ) :
    twinBitsetCountScan base lo (xs ++ ys) =
      twinBitsetCountScan base lo xs + twinBitsetCountScan base (lo + 2 * xs.sum) ys := by
  induction xs generalizing lo with
  | nil => simp [twinBitsetCountScan]
  | cons x xs ih =>
    simp only [List.cons_append, twinBitsetCountScan, List.sum_cons, ih]
    simp only [Nat.mul_add, Nat.add_assoc]

end
end Sude
