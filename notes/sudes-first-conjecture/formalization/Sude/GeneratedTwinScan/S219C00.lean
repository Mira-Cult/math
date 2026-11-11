import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21431)) 459276333 459309101 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 459276333 459309101).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21431 459276333 459309101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21432)) 459309101 459341869 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 459309101 459341869).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21432 459309101 459341869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21433)) 459341869 459374637 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 459341869 459374637).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21433 459341869 459374637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21433)) 459374637 459407405 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 459374637 459407405).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21433 459374637 459407405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 459276333 459341869).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 459276333 ≤ 459309101)
    (by decide : 459309101 ≤ 459341869) block0 block1

theorem join_0_1 : (twinPrimeSegment 459341869 459407405).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 459341869 ≤ 459374637)
    (by decide : 459374637 ≤ 459407405) block2 block3

theorem join_1_0 : (twinPrimeSegment 459276333 459407405).card = 402 := by
  simpa using combineTwinPrimeSegments (by decide : 459276333 ≤ 459341869)
    (by decide : 459341869 ≤ 459407405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 459276333 459407405).card = 402 := join_1_0

end S219C00
end Sude.GeneratedTwinScan
