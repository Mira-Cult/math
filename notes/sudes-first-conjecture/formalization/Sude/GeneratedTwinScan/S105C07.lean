import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14871)) 221118509 221151277 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221118509 221151277).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14871 221118509 221151277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14872)) 221151277 221184045 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221151277 221184045).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14872 221151277 221184045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14873)) 221184045 221216813 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221184045 221216813).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14873 221184045 221216813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14874)) 221216813 221249581 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221216813 221249581).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14874 221216813 221249581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221118509 221184045).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 221118509 ≤ 221151277)
    (by decide : 221151277 ≤ 221184045) block0 block1

theorem join_0_1 : (twinPrimeSegment 221184045 221249581).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 221184045 ≤ 221216813)
    (by decide : 221216813 ≤ 221249581) block2 block3

theorem join_1_0 : (twinPrimeSegment 221118509 221249581).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 221118509 ≤ 221184045)
    (by decide : 221184045 ≤ 221249581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221118509 221249581).card = 483 := join_1_0

end S105C07
end Sude.GeneratedTwinScan
