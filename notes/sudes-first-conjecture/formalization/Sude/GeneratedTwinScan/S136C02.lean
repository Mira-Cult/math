import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16896)) 285474861 285507629 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 285474861 285507629).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16896 285474861 285507629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16897)) 285507629 285540397 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 285507629 285540397).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16897 285507629 285540397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16898)) 285540397 285573165 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 285540397 285573165).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16898 285540397 285573165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16899)) 285573165 285605933 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 285573165 285605933).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16899 285573165 285605933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 285474861 285540397).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 285474861 ≤ 285507629)
    (by decide : 285507629 ≤ 285540397) block0 block1

theorem join_0_1 : (twinPrimeSegment 285540397 285605933).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 285540397 ≤ 285573165)
    (by decide : 285573165 ≤ 285605933) block2 block3

theorem join_1_0 : (twinPrimeSegment 285474861 285605933).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 285474861 ≤ 285540397)
    (by decide : 285540397 ≤ 285605933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 285474861 285605933).card = 465 := join_1_0

end S136C02
end Sude.GeneratedTwinScan
