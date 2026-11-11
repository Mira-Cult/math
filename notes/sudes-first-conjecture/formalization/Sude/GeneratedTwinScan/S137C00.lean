import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16951)) 287309869 287342637 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287309869 287342637).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16951 287309869 287342637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16952)) 287342637 287375405 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287342637 287375405).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16952 287342637 287375405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16953)) 287375405 287408173 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 287375405 287408173).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16953 287375405 287408173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16954)) 287408173 287440941 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 287408173 287440941).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16954 287408173 287440941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287309869 287375405).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 287309869 ≤ 287342637)
    (by decide : 287342637 ≤ 287375405) block0 block1

theorem join_0_1 : (twinPrimeSegment 287375405 287440941).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 287375405 ≤ 287408173)
    (by decide : 287408173 ≤ 287440941) block2 block3

theorem join_1_0 : (twinPrimeSegment 287309869 287440941).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 287309869 ≤ 287375405)
    (by decide : 287375405 ≤ 287440941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287309869 287440941).card = 458 := join_1_0

end S137C00
end Sude.GeneratedTwinScan
