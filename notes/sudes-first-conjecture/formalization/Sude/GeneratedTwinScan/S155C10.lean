import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18066)) 326369325 326402093 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 326369325 326402093).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18066 326369325 326402093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18067)) 326402093 326434861 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326402093 326434861).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18067 326402093 326434861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18068)) 326434861 326467629 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326434861 326467629).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18068 326434861 326467629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18069)) 326467629 326500397 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326467629 326500397).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18069 326467629 326500397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 326369325 326434861).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 326369325 ≤ 326402093)
    (by decide : 326402093 ≤ 326434861) block0 block1

theorem join_0_1 : (twinPrimeSegment 326434861 326500397).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 326434861 ≤ 326467629)
    (by decide : 326467629 ≤ 326500397) block2 block3

theorem join_1_0 : (twinPrimeSegment 326369325 326500397).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 326369325 ≤ 326434861)
    (by decide : 326434861 ≤ 326500397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 326369325 326500397).card = 435 := join_1_0

end S155C10
end Sude.GeneratedTwinScan
