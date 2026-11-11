import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13508)) 182452269 182485037 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182452269 182485037).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13508 182452269 182485037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13509)) 182485037 182517805 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 182485037 182517805).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13509 182485037 182517805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13511)) 182517805 182550573 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 182517805 182550573).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13511 182517805 182550573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13512)) 182550573 182583341 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 182550573 182583341).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13512 182550573 182583341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182452269 182517805).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 182452269 ≤ 182485037)
    (by decide : 182485037 ≤ 182517805) block0 block1

theorem join_0_1 : (twinPrimeSegment 182517805 182583341).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 182517805 ≤ 182550573)
    (by decide : 182550573 ≤ 182583341) block2 block3

theorem join_1_0 : (twinPrimeSegment 182452269 182583341).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 182452269 ≤ 182517805)
    (by decide : 182517805 ≤ 182583341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182452269 182583341).card = 449 := join_1_0

end S087C00
end Sude.GeneratedTwinScan
