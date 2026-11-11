import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14800)) 219021357 219054125 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219021357 219054125).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14800 219021357 219054125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14801)) 219054125 219086893 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219054125 219086893).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14801 219054125 219086893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14802)) 219086893 219119661 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 219086893 219119661).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14802 219086893 219119661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14803)) 219119661 219152429 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 219119661 219152429).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14803 219119661 219152429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219021357 219086893).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 219021357 ≤ 219054125)
    (by decide : 219054125 ≤ 219086893) block0 block1

theorem join_0_1 : (twinPrimeSegment 219086893 219152429).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 219086893 ≤ 219119661)
    (by decide : 219119661 ≤ 219152429) block2 block3

theorem join_1_0 : (twinPrimeSegment 219021357 219152429).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 219021357 ≤ 219086893)
    (by decide : 219086893 ≤ 219152429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219021357 219152429).card = 442 := join_1_0

end S104C07
end Sude.GeneratedTwinScan
