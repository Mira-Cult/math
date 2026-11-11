import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16268)) 264634413 264667181 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 264634413 264667181).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16268 264634413 264667181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16269)) 264667181 264699949 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264667181 264699949).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16269 264667181 264699949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16270)) 264699949 264732717 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264699949 264732717).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16270 264699949 264732717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16271)) 264732717 264765485 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264732717 264765485).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16271 264732717 264765485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 264634413 264699949).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 264634413 ≤ 264667181)
    (by decide : 264667181 ≤ 264699949) block0 block1

theorem join_0_1 : (twinPrimeSegment 264699949 264765485).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 264699949 ≤ 264732717)
    (by decide : 264732717 ≤ 264765485) block2 block3

theorem join_1_0 : (twinPrimeSegment 264634413 264765485).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 264634413 ≤ 264699949)
    (by decide : 264699949 ≤ 264765485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 264634413 264765485).card = 449 := join_1_0

end S126C03
end Sude.GeneratedTwinScan
