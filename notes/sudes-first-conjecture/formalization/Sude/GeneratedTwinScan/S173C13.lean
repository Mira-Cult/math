import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19093)) 364511277 364544045 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 364511277 364544045).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19093 364511277 364544045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19093)) 364544045 364576813 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364544045 364576813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19093 364544045 364576813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19094)) 364576813 364609581 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364576813 364609581).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19094 364576813 364609581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19095)) 364609581 364642349 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 364609581 364642349).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19095 364609581 364642349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 364511277 364576813).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 364511277 ≤ 364544045)
    (by decide : 364544045 ≤ 364576813) block0 block1

theorem join_0_1 : (twinPrimeSegment 364576813 364642349).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 364576813 ≤ 364609581)
    (by decide : 364609581 ≤ 364642349) block2 block3

theorem join_1_0 : (twinPrimeSegment 364511277 364642349).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 364511277 ≤ 364576813)
    (by decide : 364576813 ≤ 364642349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 364511277 364642349).card = 451 := join_1_0

end S173C13
end Sude.GeneratedTwinScan
