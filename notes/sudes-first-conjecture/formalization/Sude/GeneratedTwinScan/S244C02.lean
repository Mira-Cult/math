import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22627)) 511967277 512000045 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511967277 512000045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22627 511967277 512000045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22628)) 512000045 512032813 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512000045 512032813).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22628 512000045 512032813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22628)) 512032813 512065581 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512032813 512065581).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22628 512032813 512065581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22629)) 512065581 512098349 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512065581 512098349).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22629 512065581 512098349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511967277 512032813).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 511967277 ≤ 512000045)
    (by decide : 512000045 ≤ 512032813) block0 block1

theorem join_0_1 : (twinPrimeSegment 512032813 512098349).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 512032813 ≤ 512065581)
    (by decide : 512065581 ≤ 512098349) block2 block3

theorem join_1_0 : (twinPrimeSegment 511967277 512098349).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 511967277 ≤ 512032813)
    (by decide : 512032813 ≤ 512098349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511967277 512098349).card = 422 := join_1_0

end S244C02
end Sude.GeneratedTwinScan
