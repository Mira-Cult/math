import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22102)) 488505389 488538157 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 488505389 488538157).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22102 488505389 488538157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22103)) 488538157 488570925 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 488538157 488570925).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22103 488538157 488570925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22104)) 488570925 488603693 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 488570925 488603693).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22104 488570925 488603693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22105)) 488603693 488636461 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 488603693 488636461).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22105 488603693 488636461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 488505389 488570925).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 488505389 ≤ 488538157)
    (by decide : 488538157 ≤ 488570925) block0 block1

theorem join_0_1 : (twinPrimeSegment 488570925 488636461).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 488570925 ≤ 488603693)
    (by decide : 488603693 ≤ 488636461) block2 block3

theorem join_1_0 : (twinPrimeSegment 488505389 488636461).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 488505389 ≤ 488570925)
    (by decide : 488570925 ≤ 488636461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 488505389 488636461).card = 458 := join_1_0

end S232C15
end Sude.GeneratedTwinScan
