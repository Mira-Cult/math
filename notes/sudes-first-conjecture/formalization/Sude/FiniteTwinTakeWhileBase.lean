import Sude.FiniteTwinFilteredBase

/-! A sorted-prefix form of the checked finite twin prime base. -/
namespace Sude

/-- On a strictly increasing list, taking the initial entries at most B is
identical to filtering the entire list at B. -/
theorem sorted_lt_takeWhile_le_eq_filter (xs : List ℕ) (B : ℕ)
    (hxs : xs.SortedLT) :
    xs.takeWhile (fun p => p ≤ B) = xs.filter (fun p => p ≤ B) := by
  have hpair : xs.Pairwise (· < ·) := hxs.pairwise
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have h := List.pairwise_cons.mp hpair
      by_cases hx : x ≤ B
      · simp only [List.takeWhile_cons, List.filter_cons, decide_eq_true_eq, hx,
          ↓reduceIte]
        exact congrArg (List.cons x) (ih h.2.sortedLT h.2)
      · have htail : ∀ y ∈ xs, ¬ y ≤ B := by
          intro y hy hle
          have hxy := h.1 y hy
          omega
        have hf : xs.filter (fun p => p ≤ B) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro y hy
          simpa only [decide_eq_true_eq] using htail y hy
        simp [hx, hf]

/-- The explicit complete checked base is strictly increasing, including 2. -/
theorem finiteTwinCheckedBase_sorted : finiteTwinCheckedBase.SortedLT := by
  apply List.Pairwise.sortedLT
  rw [finiteTwinCheckedBase, List.pairwise_cons]
  refine ⟨?_, finiteTwinOddBase_sorted.pairwise⟩
  intro p hp
  have h := finiteTwinOddBase_valid p hp
  omega

/-- On the checked base, the bounded prefix and complete bounded filter agree. -/
theorem finiteTwinCheckedBase_takeWhile_eq_filter (B : ℕ) :
    finiteTwinCheckedBase.takeWhile (fun p => p ≤ B) =
      finiteTwinCheckedBase.filter (fun p => p ≤ B) :=
  sorted_lt_takeWhile_le_eq_filter finiteTwinCheckedBase B finiteTwinCheckedBase_sorted

/-- The prefix retains a complete prime base through any bound in the
verified base range. -/
theorem finiteTwinCheckedBase_takeWhile_complete (B : ℕ) (hB : B ≤ 32768) :
    CompletePrimeBase (finiteTwinCheckedBase.takeWhile (fun p => p ≤ B)).toFinset B := by
  rw [finiteTwinCheckedBase_takeWhile_eq_filter]
  exact finite_twin_filtered_base_complete B hB

/-- The compressed scanner on the prefix counts the mathematical segment,
provided the explicit padded lookahead fits the truncated base. -/
theorem finiteTwinTakeWhile_compressed_interval_spec (B lo hi : ℕ)
    (hB : B ≤ 32768) (hlo : 5 ≤ lo)
    (hlook : strideSixFirst lo + 2 * (3 * strideSixWidth lo hi + 1) ≤
      (B + 1) * (B + 1)) :
    strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ B)) lo hi =
      (twinPrimeSegment lo hi).card :=
  strideSixCompressedIntervalScan_spec _ B lo hi
    (finiteTwinCheckedBase_takeWhile_complete B hB) hlo hlook

end Sude
