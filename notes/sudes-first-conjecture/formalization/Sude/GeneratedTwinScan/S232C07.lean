import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S232C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22079)) 487456813 487489581 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 487456813 487489581).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22079 487456813 487489581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22079)) 487489581 487522349 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 487489581 487522349).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22079 487489581 487522349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22080)) 487522349 487555117 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 487522349 487555117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22080 487522349 487555117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22081)) 487555117 487587885 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 487555117 487587885).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22081 487555117 487587885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 487456813 487522349).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 487456813 ≤ 487489581)
    (by decide : 487489581 ≤ 487522349) block0 block1

theorem join_0_1 : (twinPrimeSegment 487522349 487587885).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 487522349 ≤ 487555117)
    (by decide : 487555117 ≤ 487587885) block2 block3

theorem join_1_0 : (twinPrimeSegment 487456813 487587885).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 487456813 ≤ 487522349)
    (by decide : 487522349 ≤ 487587885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 487456813 487587885).card = 436 := join_1_0

end S232C07
end Sude.GeneratedTwinScan
