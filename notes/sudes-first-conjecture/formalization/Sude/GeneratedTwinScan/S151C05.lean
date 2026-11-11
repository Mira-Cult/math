import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17814)) 317325357 317358125 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 317325357 317358125).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17814 317325357 317358125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17815)) 317358125 317390893 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 317358125 317390893).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17815 317358125 317390893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17816)) 317390893 317423661 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 317390893 317423661).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17816 317390893 317423661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17817)) 317423661 317456429 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 317423661 317456429).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17817 317423661 317456429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 317325357 317390893).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 317325357 ≤ 317358125)
    (by decide : 317358125 ≤ 317390893) block0 block1

theorem join_0_1 : (twinPrimeSegment 317390893 317456429).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 317390893 ≤ 317423661)
    (by decide : 317423661 ≤ 317456429) block2 block3

theorem join_1_0 : (twinPrimeSegment 317325357 317456429).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 317325357 ≤ 317390893)
    (by decide : 317390893 ≤ 317456429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 317325357 317456429).card = 476 := join_1_0

end S151C05
end Sude.GeneratedTwinScan
