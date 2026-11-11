import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22291)) 496893997 496926765 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 496893997 496926765).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22291 496893997 496926765
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22292)) 496926765 496959533 = 91 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496926765 496959533).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22292 496926765 496959533
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22293)) 496959533 496992301 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496959533 496992301).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22293 496959533 496992301
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22294)) 496992301 497025069 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496992301 497025069).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22294 496992301 497025069
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 496893997 496959533).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 496893997 ≤ 496926765)
    (by decide : 496926765 ≤ 496959533) block0 block1

theorem join_0_1 : (twinPrimeSegment 496959533 497025069).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 496959533 ≤ 496992301)
    (by decide : 496992301 ≤ 497025069) block2 block3

theorem join_1_0 : (twinPrimeSegment 496893997 497025069).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 496893997 ≤ 496959533)
    (by decide : 496959533 ≤ 497025069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 496893997 497025069).card = 425 := join_1_0

end S236C15
end Sude.GeneratedTwinScan
