import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S111C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15318)) 234618925 234651693 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 234618925 234651693).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15318 234618925 234651693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15319)) 234651693 234684461 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 234651693 234684461).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15319 234651693 234684461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15320)) 234684461 234717229 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 234684461 234717229).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15320 234684461 234717229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15321)) 234717229 234749997 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 234717229 234749997).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15321 234717229 234749997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 234618925 234684461).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 234618925 ≤ 234651693)
    (by decide : 234651693 ≤ 234684461) block0 block1

theorem join_0_1 : (twinPrimeSegment 234684461 234749997).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 234684461 ≤ 234717229)
    (by decide : 234717229 ≤ 234749997) block2 block3

theorem join_1_0 : (twinPrimeSegment 234618925 234749997).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 234618925 ≤ 234684461)
    (by decide : 234684461 ≤ 234749997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 234618925 234749997).card = 489 := join_1_0

end S111C14
end Sude.GeneratedTwinScan
