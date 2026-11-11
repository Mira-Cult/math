import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12589)) 158466093 158498861 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 158466093 158498861).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12589 158466093 158498861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12590)) 158498861 158531629 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 158498861 158531629).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12590 158498861 158531629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12592)) 158531629 158564397 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 158531629 158564397).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12592 158531629 158564397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12593)) 158564397 158597165 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 158564397 158597165).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12593 158564397 158597165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 158466093 158531629).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 158466093 ≤ 158498861)
    (by decide : 158498861 ≤ 158531629) block0 block1

theorem join_0_1 : (twinPrimeSegment 158531629 158597165).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 158531629 ≤ 158564397)
    (by decide : 158564397 ≤ 158597165) block2 block3

theorem join_1_0 : (twinPrimeSegment 158466093 158597165).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 158466093 ≤ 158531629)
    (by decide : 158531629 ≤ 158597165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 158466093 158597165).card = 485 := join_1_0

end S075C09
end Sude.GeneratedTwinScan
