import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14309)) 204734509 204767277 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204734509 204767277).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14309 204734509 204767277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14310)) 204767277 204800045 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204767277 204800045).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14310 204767277 204800045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14311)) 204800045 204832813 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204800045 204832813).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14311 204800045 204832813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14313)) 204832813 204865581 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204832813 204865581).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14313 204832813 204865581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204734509 204800045).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 204734509 ≤ 204767277)
    (by decide : 204767277 ≤ 204800045) block0 block1

theorem join_0_1 : (twinPrimeSegment 204800045 204865581).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 204800045 ≤ 204832813)
    (by decide : 204832813 ≤ 204865581) block2 block3

theorem join_1_0 : (twinPrimeSegment 204734509 204865581).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 204734509 ≤ 204800045)
    (by decide : 204800045 ≤ 204865581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204734509 204865581).card = 502 := join_1_0

end S097C10
end Sude.GeneratedTwinScan
