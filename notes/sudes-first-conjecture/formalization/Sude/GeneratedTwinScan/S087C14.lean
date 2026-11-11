import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13576)) 184287277 184320045 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 184287277 184320045).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13576 184287277 184320045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13577)) 184320045 184352813 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 184320045 184352813).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13577 184320045 184352813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13578)) 184352813 184385581 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 184352813 184385581).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13578 184352813 184385581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13580)) 184385581 184418349 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 184385581 184418349).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13580 184385581 184418349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 184287277 184352813).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 184287277 ≤ 184320045)
    (by decide : 184320045 ≤ 184352813) block0 block1

theorem join_0_1 : (twinPrimeSegment 184352813 184418349).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 184352813 ≤ 184385581)
    (by decide : 184385581 ≤ 184418349) block2 block3

theorem join_1_0 : (twinPrimeSegment 184287277 184418349).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 184287277 ≤ 184352813)
    (by decide : 184352813 ≤ 184418349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 184287277 184418349).card = 468 := join_1_0

end S087C14
end Sude.GeneratedTwinScan
