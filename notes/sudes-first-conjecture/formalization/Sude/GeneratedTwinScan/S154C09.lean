import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18004)) 324141101 324173869 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324141101 324173869).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18004 324141101 324173869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18005)) 324173869 324206637 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324173869 324206637).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18005 324173869 324206637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18006)) 324206637 324239405 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324206637 324239405).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18006 324206637 324239405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18007)) 324239405 324272173 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324239405 324272173).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18007 324239405 324272173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324141101 324206637).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 324141101 ≤ 324173869)
    (by decide : 324173869 ≤ 324206637) block0 block1

theorem join_0_1 : (twinPrimeSegment 324206637 324272173).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 324206637 ≤ 324239405)
    (by decide : 324239405 ≤ 324272173) block2 block3

theorem join_1_0 : (twinPrimeSegment 324141101 324272173).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 324141101 ≤ 324206637)
    (by decide : 324206637 ≤ 324272173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324141101 324272173).card = 412 := join_1_0

end S154C09
end Sude.GeneratedTwinScan
