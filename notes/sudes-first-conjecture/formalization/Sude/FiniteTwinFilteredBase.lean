import Sude.FiniteTwinOddBaseComplete
import Sude.TwinStrideSixCompressed

/-! A checked prime base can be truncated for a smaller scan bound. The
scanner's padded lookahead condition remains an explicit hypothesis. -/
namespace Sude
noncomputable section

/-- Filtering a complete prime base at a smaller bound retains precisely the
primes up to that bound. -/
theorem complete_prime_base_filter_le (base : List ℕ) (upper bound : ℕ)
    (hbase : CompletePrimeBase base.toFinset upper) (hbound : bound ≤ upper) :
    CompletePrimeBase (base.filter (· ≤ bound)).toFinset bound := by
  intro p
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  rw [← List.mem_toFinset, hbase p]
  constructor
  · rintro ⟨⟨hp, _⟩, hb⟩
    exact ⟨hp, hb⟩
  · rintro ⟨hp, hb⟩
    exact ⟨⟨hp, le_trans hb hbound⟩, hb⟩

/-- The previously verified finite base is complete after truncation to any
bound within its proved range. -/
theorem finite_twin_filtered_base_complete (bound : ℕ) (hbound : bound ≤ 32768) :
    CompletePrimeBase (finiteTwinCheckedBase.filter (· ≤ bound)).toFinset bound :=
  complete_prime_base_filter_le finiteTwinCheckedBase 32768 bound
    finiteTwinCheckedBase_complete hbound

/-- The truncated compressed scanner still counts exactly the mathematical
half-open lower-endpoint segment, including its padded upper lookahead. -/
theorem finite_twin_filtered_compressed_interval_spec (bound lo hi : ℕ)
    (hbound : bound ≤ 32768) (hlo : 5 ≤ lo)
    (hlook : strideSixFirst lo + 2 * (3 * strideSixWidth lo hi + 1) ≤
      (bound + 1) * (bound + 1)) :
    strideSixCompressedIntervalScan (finiteTwinCheckedBase.filter (· ≤ bound)) lo hi =
      (twinPrimeSegment lo hi).card :=
  strideSixCompressedIntervalScan_spec _ bound lo hi
    (finite_twin_filtered_base_complete bound hbound) hlo hlook

end
end Sude
