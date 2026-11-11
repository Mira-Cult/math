import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S190C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19981)) 399245357 399278125 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 399245357 399278125).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19981 399245357 399278125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19982)) 399278125 399310893 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 399278125 399310893).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19982 399278125 399310893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19983)) 399310893 399343661 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 399310893 399343661).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19983 399310893 399343661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19984)) 399343661 399376429 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 399343661 399376429).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19984 399343661 399376429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 399245357 399310893).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 399245357 ≤ 399278125)
    (by decide : 399278125 ≤ 399310893) block0 block1

theorem join_0_1 : (twinPrimeSegment 399310893 399376429).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 399310893 ≤ 399343661)
    (by decide : 399343661 ≤ 399376429) block2 block3

theorem join_1_0 : (twinPrimeSegment 399245357 399376429).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 399245357 ≤ 399310893)
    (by decide : 399310893 ≤ 399376429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 399245357 399376429).card = 449 := join_1_0

end S190C06
end Sude.GeneratedTwinScan
