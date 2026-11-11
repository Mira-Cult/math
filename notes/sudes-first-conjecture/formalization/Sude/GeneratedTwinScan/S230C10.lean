import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21992)) 483655725 483688493 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483655725 483688493).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21992 483655725 483688493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21993)) 483688493 483721261 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483688493 483721261).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21993 483688493 483721261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21994)) 483721261 483754029 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483721261 483754029).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21994 483721261 483754029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21995)) 483754029 483786797 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483754029 483786797).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21995 483754029 483786797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483655725 483721261).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 483655725 ≤ 483688493)
    (by decide : 483688493 ≤ 483721261) block0 block1

theorem join_0_1 : (twinPrimeSegment 483721261 483786797).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 483721261 ≤ 483754029)
    (by decide : 483754029 ≤ 483786797) block2 block3

theorem join_1_0 : (twinPrimeSegment 483655725 483786797).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 483655725 ≤ 483721261)
    (by decide : 483721261 ≤ 483786797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483655725 483786797).card = 416 := join_1_0

end S230C10
end Sude.GeneratedTwinScan
