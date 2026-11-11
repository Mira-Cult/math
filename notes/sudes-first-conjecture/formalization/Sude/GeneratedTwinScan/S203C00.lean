import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S203C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20633)) 425721901 425754669 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 425721901 425754669).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20633 425721901 425754669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20634)) 425754669 425787437 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 425754669 425787437).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20634 425754669 425787437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20635)) 425787437 425820205 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 425787437 425820205).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20635 425787437 425820205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20636)) 425820205 425852973 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 425820205 425852973).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20636 425820205 425852973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 425721901 425787437).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 425721901 ≤ 425754669)
    (by decide : 425754669 ≤ 425787437) block0 block1

theorem join_0_1 : (twinPrimeSegment 425787437 425852973).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 425787437 ≤ 425820205)
    (by decide : 425820205 ≤ 425852973) block2 block3

theorem join_1_0 : (twinPrimeSegment 425721901 425852973).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 425721901 ≤ 425787437)
    (by decide : 425787437 ≤ 425852973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 425721901 425852973).card = 446 := join_1_0

end S203C00
end Sude.GeneratedTwinScan
