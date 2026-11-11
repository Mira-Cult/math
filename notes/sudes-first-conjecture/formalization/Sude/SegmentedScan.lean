import Sude.MarkedPrefix

/-! A kernel-reconstructible segmented prefix scan over proved marking sets.
Acceptance of a tail-sized scan remains an explicit obligation. -/
namespace Sude
noncomputable section

/-- Count and sum the values represented by unmarked indices. -/
def markingSegmentSummary (base : Finset ℕ) (lo width : ℕ) : ℕ × ℕ :=
  ((unmarkedIndices base lo width).card,
    (∑ i ∈ unmarkedIndices base lo width, (lo + 2 * i)))

/-- Summary correctness follows from the actual set of unmarked indices,
including exact injectivity of the odd-value indexing. -/
theorem markingSegmentSummary_spec (base : Finset ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base bound) (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * width ≤ (bound + 1) * (bound + 1)) :
    markingSegmentSummary base lo width =
      ((oddPrimeSegment lo (lo + 2 * width)).card,
        ∑ p ∈ oddPrimeSegment lo (lo + 2 * width), p) := by
  classical
  have hset := markedSieveValues_spec base bound lo width hbase hlo hodd hbound
  have hinj : Function.Injective (fun i : ℕ => lo + 2 * i) := by
    intro i j h
    dsimp at h
    omega
  rw [← hset]
  simp [markingSegmentSummary, markedSieveValues, Finset.card_image_iff.mpr hinj.injOn,
    Finset.sum_image, hinj.injOn]

/-- Add summaries of adjacent odd-indexed segments. Each recursive step
begins where the preceding half-open segment ended. -/
def markingSegmentScan (base : Finset ℕ) (lo : ℕ) : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | width :: widths =>
    let here := markingSegmentSummary base lo width
    let rest := markingSegmentScan base (lo + 2 * width) widths
    (here.1 + rest.1, here.2 + rest.2)

/-- A total-width plan of equal chunks and one final remainder. The zero
chunk case remains a well-defined finite plan; useful scans take chunk > 0. -/
def uniformSegmentWidths (total chunk : ℕ) : List ℕ :=
  List.replicate (total / chunk) chunk ++ [total % chunk]

theorem uniformSegmentWidths_sum (total chunk : ℕ) :
    (uniformSegmentWidths total chunk).sum = total := by
  simp only [uniformSegmentWidths, List.sum_append, List.sum_replicate,
    List.sum_cons, List.sum_nil, add_zero, nsmul_eq_mul]
  simpa [Nat.mul_comm] using Nat.div_add_mod total chunk

/-- Independently verified groups of segments can be composed without
re-evaluating either group's scan. -/
theorem markingSegmentScan_append (base : Finset ℕ) (lo : ℕ) (xs ys : List ℕ) :
    markingSegmentScan base lo (xs ++ ys) =
      ((markingSegmentScan base lo xs).1 +
          (markingSegmentScan base (lo + 2 * xs.sum) ys).1,
        (markingSegmentScan base lo xs).2 +
          (markingSegmentScan base (lo + 2 * xs.sum) ys).2) := by
  induction xs generalizing lo with
  | nil => simp [markingSegmentScan]
  | cons w ws ih =>
    simp only [List.cons_append, List.sum_cons, markingSegmentScan]
    rw [ih]
    have hpos : lo + 2 * w + 2 * ws.sum = lo + 2 * (w + ws.sum) := by omega
    simp only [hpos, Nat.add_assoc]

/-- Mathematical odd-prime intervals concatenate exactly. -/
theorem oddPrimeSegment_additive {lo mid hi : ℕ} (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    (oddPrimeSegment lo hi).card =
      (oddPrimeSegment lo mid).card + (oddPrimeSegment mid hi).card ∧
    (∑ p ∈ oddPrimeSegment lo hi, p) =
      (∑ p ∈ oddPrimeSegment lo mid, p) + (∑ p ∈ oddPrimeSegment mid hi, p) := by
  have hdisj : Disjoint (oddPrimeSegment lo mid) (oddPrimeSegment mid hi) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [oddPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp hq
    omega
  have hunion : oddPrimeSegment lo mid ∪ oddPrimeSegment mid hi = oddPrimeSegment lo hi := by
    ext p
    simp only [oddPrimeSegment, Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro (⟨⟨hlo, hmid⟩, hp, hne⟩ | ⟨⟨hmid, hhi⟩, hp, hne⟩)
      · exact ⟨⟨hlo, by omega⟩, hp, hne⟩
      · exact ⟨⟨by omega, hhi⟩, hp, hne⟩
    · rintro ⟨⟨hlo, hhi⟩, hp, hne⟩
      by_cases h : p < mid
      · exact Or.inl ⟨⟨hlo, h⟩, hp, hne⟩
      · exact Or.inr ⟨⟨by omega, hhi⟩, hp, hne⟩
  rw [← hunion, Finset.card_union_of_disjoint hdisj, Finset.sum_union hdisj]
  exact ⟨rfl, rfl⟩

/-- Any finite list of segment widths yields the exact count and sum through
its combined width, including zero-width segments. -/
theorem markingSegmentScan_spec (base : Finset ℕ) (bound lo : ℕ) (widths : List ℕ)
    (hbase : CompletePrimeBase base bound) (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * widths.sum ≤ (bound + 1) * (bound + 1)) :
    markingSegmentScan base lo widths =
      ((oddPrimeSegment lo (lo + 2 * widths.sum)).card,
        ∑ p ∈ oddPrimeSegment lo (lo + 2 * widths.sum), p) := by
  induction widths generalizing lo with
  | nil =>
    simp [markingSegmentScan, oddPrimeSegment]
  | cons width widths ih =>
    have hone : lo + 2 * width ≤ (bound + 1) * (bound + 1) := by
      simp only [List.sum_cons] at hbound
      omega
    have htail : lo + 2 * width + 2 * widths.sum ≤ (bound + 1) * (bound + 1) := by
      simp only [List.sum_cons] at hbound
      omega
    have hodd' : (lo + 2 * width) % 2 = 1 := by omega
    have hs := markingSegmentSummary_spec base bound lo width hbase hlo hodd hone
    have ht := ih (lo + 2 * width) (by omega) hodd' htail
    have hsum := oddPrimeSegment_additive (lo := lo) (mid := lo + 2 * width)
      (hi := lo + 2 * width + 2 * widths.sum) (by omega) (by omega)
    simp only [markingSegmentScan, hs, ht, List.sum_cons]
    have hend : lo + 2 * (width + widths.sum) = lo + 2 * width + 2 * widths.sum := by omega
    rw [hend, hsum.1, hsum.2]

/-- A scan whose combined width ends at the odd endpoint X is exactly the
odd-prime prefix count and sum. -/
theorem markingSegmentScan_prefix (base : Finset ℕ) (bound X : ℕ) (widths : List ℕ)
    (hbase : CompletePrimeBase base bound) (hX : 3 ≤ X) (hodd : X % 2 = 1)
    (hwidth : widths.sum = (X - 3) / 2 + 1)
    (hbound : X + 2 ≤ (bound + 1) * (bound + 1)) :
    markingSegmentScan base 3 widths =
      ((oddPrimePrefix X).card, ∑ p ∈ oddPrimePrefix X, p) := by
  have hend : 3 + 2 * widths.sum = X + 2 := by rw [hwidth]; omega
  have hscan := markingSegmentScan_spec base bound 3 widths hbase (by decide) (by decide) (by omega)
  have hsegment : oddPrimeSegment 3 (3 + 2 * widths.sum) = oddPrimePrefix X := by
    rw [hwidth]
    exact (markedSieveValues_spec base bound 3 ((X - 3) / 2 + 1) hbase
      (by decide) (by decide) (by omega)).symm.trans
      (markedSieve_prefix base bound X hbase hX hodd hbound)
  simpa only [hsegment] using hscan

/-- Kernel acceptance of the segmented scan, together with endpoint
primality, proves the exact prescribed pool identities. -/
theorem markingSegmentScan_pool_identities (base : Finset ℕ) (bound n X T : ℕ)
    (widths : List ℕ) (hbase : CompletePrimeBase base bound) (hX : Nat.Prime X)
    (hX3 : 3 ≤ X) (hodd : X % 2 = 1)
    (hwidth : widths.sum = (X - 3) / 2 + 1)
    (hbound : X + 2 ≤ (bound + 1) * (bound + 1))
    (hscan : markingSegmentScan base 3 widths = (n * n, T)) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  have hspec := markingSegmentScan_prefix base bound X widths hbase hX3 hodd hwidth hbound
  rw [hscan] at hspec
  have hcount : (oddPrimePrefix X).card = n * n := by
    have h := congrArg Prod.fst hspec
    simpa using h.symm
  have hsum : (∑ p ∈ oddPrimePrefix X, p) = T := by
    have h := congrArg Prod.snd hspec
    simpa using h.symm
  exact pool_identities_of_oddPrefix_certificate hX hcount hsum

/-- Fixed-width segmentation of the entire odd prefix, with the final
remainder handled exactly. The scan acceptance remains a separate premise. -/
theorem uniformScan_pool_identities (base : Finset ℕ) (bound n X T chunk : ℕ)
    (hbase : CompletePrimeBase base bound) (hX : Nat.Prime X)
    (hX3 : 3 ≤ X) (hodd : X % 2 = 1)
    (hbound : X + 2 ≤ (bound + 1) * (bound + 1))
    (hscan : markingSegmentScan base 3
      (uniformSegmentWidths ((X - 3) / 2 + 1) chunk) = (n * n, T)) :
    poolMaximum n = X ∧ Lucas.poolTotal n = T := by
  exact markingSegmentScan_pool_identities base bound n X T _ hbase hX hX3 hodd
    (uniformSegmentWidths_sum _ _) hbound hscan

end
end Sude
