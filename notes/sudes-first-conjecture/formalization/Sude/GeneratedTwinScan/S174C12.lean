import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19144)) 366477357 366510125 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366477357 366510125).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19144 366477357 366510125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19145)) 366510125 366542893 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366510125 366542893).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19145 366510125 366542893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19146)) 366542893 366575661 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366542893 366575661).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19146 366542893 366575661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19147)) 366575661 366608429 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366575661 366608429).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19147 366575661 366608429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366477357 366542893).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 366477357 ≤ 366510125)
    (by decide : 366510125 ≤ 366542893) block0 block1

theorem join_0_1 : (twinPrimeSegment 366542893 366608429).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 366542893 ≤ 366575661)
    (by decide : 366575661 ≤ 366608429) block2 block3

theorem join_1_0 : (twinPrimeSegment 366477357 366608429).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 366477357 ≤ 366542893)
    (by decide : 366542893 ≤ 366608429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366477357 366608429).card = 478 := join_1_0

end S174C12
end Sude.GeneratedTwinScan
