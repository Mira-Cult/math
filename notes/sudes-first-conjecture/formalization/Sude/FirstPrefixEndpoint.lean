import Sude.GeneratedFTT.R0000

/-! A kernel-checked Lucas certificate for the endpoint X recorded in the
first FC2K target row. Its prime index and prefix sum remain unproved. -/
namespace Sude.Lucas.Generated
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem first_ftt_max_prime : Nat.Prime R0000.row_2001.maxEntry := by
  change Nat.Prime 67939607
  apply nodeValid_prime [2, 7, 1471, 3299]
    ⟨67939607, 5, [(2, 1), (7, 1), (1471, 1), (3299, 1)]⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> norm_num
  · decide +kernel

end Sude.Lucas.Generated
