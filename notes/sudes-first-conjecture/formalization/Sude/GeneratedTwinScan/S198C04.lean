import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20391)) 415760429 415793197 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 415760429 415793197).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20391 415760429 415793197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20391)) 415793197 415825965 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 415793197 415825965).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20391 415793197 415825965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20392)) 415825965 415858733 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 415825965 415858733).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20392 415825965 415858733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20393)) 415858733 415891501 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 415858733 415891501).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20393 415858733 415891501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 415760429 415825965).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 415760429 ≤ 415793197)
    (by decide : 415793197 ≤ 415825965) block0 block1

theorem join_0_1 : (twinPrimeSegment 415825965 415891501).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 415825965 ≤ 415858733)
    (by decide : 415858733 ≤ 415891501) block2 block3

theorem join_1_0 : (twinPrimeSegment 415760429 415891501).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 415760429 ≤ 415825965)
    (by decide : 415825965 ≤ 415891501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 415760429 415891501).card = 432 := join_1_0

end S198C04
end Sude.GeneratedTwinScan
