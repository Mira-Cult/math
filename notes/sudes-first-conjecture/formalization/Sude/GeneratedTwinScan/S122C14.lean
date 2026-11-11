import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16053)) 257687597 257720365 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 257687597 257720365).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16053 257687597 257720365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16054)) 257720365 257753133 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 257720365 257753133).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16054 257720365 257753133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16055)) 257753133 257785901 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 257753133 257785901).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16055 257753133 257785901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16056)) 257785901 257818669 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 257785901 257818669).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16056 257785901 257818669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 257687597 257753133).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 257687597 ≤ 257720365)
    (by decide : 257720365 ≤ 257753133) block0 block1

theorem join_0_1 : (twinPrimeSegment 257753133 257818669).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 257753133 ≤ 257785901)
    (by decide : 257785901 ≤ 257818669) block2 block3

theorem join_1_0 : (twinPrimeSegment 257687597 257818669).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 257687597 ≤ 257753133)
    (by decide : 257753133 ≤ 257818669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 257687597 257818669).card = 455 := join_1_0

end S122C14
end Sude.GeneratedTwinScan
