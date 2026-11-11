import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19341)) 374079533 374112301 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374079533 374112301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19341 374079533 374112301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19342)) 374112301 374145069 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 374112301 374145069).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19342 374112301 374145069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19343)) 374145069 374177837 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374145069 374177837).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19343 374145069 374177837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19344)) 374177837 374210605 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374177837 374210605).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19344 374177837 374210605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374079533 374145069).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 374079533 ≤ 374112301)
    (by decide : 374112301 ≤ 374145069) block0 block1

theorem join_0_1 : (twinPrimeSegment 374145069 374210605).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 374145069 ≤ 374177837)
    (by decide : 374177837 ≤ 374210605) block2 block3

theorem join_1_0 : (twinPrimeSegment 374079533 374210605).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 374079533 ≤ 374145069)
    (by decide : 374145069 ≤ 374210605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374079533 374210605).card = 451 := join_1_0

end S178C06
end Sude.GeneratedTwinScan
