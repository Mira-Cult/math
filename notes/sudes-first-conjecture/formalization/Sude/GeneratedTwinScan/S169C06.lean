import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18847)) 355205165 355237933 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 355205165 355237933).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18847 355205165 355237933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18848)) 355237933 355270701 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 355237933 355270701).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18848 355237933 355270701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18849)) 355270701 355303469 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 355270701 355303469).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18849 355270701 355303469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18850)) 355303469 355336237 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 355303469 355336237).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18850 355303469 355336237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 355205165 355270701).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 355205165 ≤ 355237933)
    (by decide : 355237933 ≤ 355270701) block0 block1

theorem join_0_1 : (twinPrimeSegment 355270701 355336237).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 355270701 ≤ 355303469)
    (by decide : 355303469 ≤ 355336237) block2 block3

theorem join_1_0 : (twinPrimeSegment 355205165 355336237).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 355205165 ≤ 355270701)
    (by decide : 355270701 ≤ 355336237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 355205165 355336237).card = 471 := join_1_0

end S169C06
end Sude.GeneratedTwinScan
