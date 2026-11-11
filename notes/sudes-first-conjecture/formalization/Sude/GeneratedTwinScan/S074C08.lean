import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12500)) 156237869 156270637 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 156237869 156270637).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12500 156237869 156270637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12502)) 156270637 156303405 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 156270637 156303405).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12502 156270637 156303405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12503)) 156303405 156336173 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 156303405 156336173).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12503 156303405 156336173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12504)) 156336173 156368941 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 156336173 156368941).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12504 156336173 156368941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 156237869 156303405).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 156237869 ≤ 156270637)
    (by decide : 156270637 ≤ 156303405) block0 block1

theorem join_0_1 : (twinPrimeSegment 156303405 156368941).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 156303405 ≤ 156336173)
    (by decide : 156336173 ≤ 156368941) block2 block3

theorem join_1_0 : (twinPrimeSegment 156237869 156368941).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 156237869 ≤ 156303405)
    (by decide : 156303405 ≤ 156368941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 156237869 156368941).card = 462 := join_1_0

end S074C08
end Sude.GeneratedTwinScan
