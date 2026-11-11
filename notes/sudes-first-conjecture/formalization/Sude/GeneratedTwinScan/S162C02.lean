import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18439)) 340000813 340033581 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340000813 340033581).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18439 340000813 340033581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18440)) 340033581 340066349 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340033581 340066349).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18440 340033581 340066349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18441)) 340066349 340099117 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340066349 340099117).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18441 340066349 340099117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18442)) 340099117 340131885 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340099117 340131885).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18442 340099117 340131885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340000813 340066349).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 340000813 ≤ 340033581)
    (by decide : 340033581 ≤ 340066349) block0 block1

theorem join_0_1 : (twinPrimeSegment 340066349 340131885).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 340066349 ≤ 340099117)
    (by decide : 340099117 ≤ 340131885) block2 block3

theorem join_1_0 : (twinPrimeSegment 340000813 340131885).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 340000813 ≤ 340066349)
    (by decide : 340066349 ≤ 340131885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340000813 340131885).card = 491 := join_1_0

end S162C02
end Sude.GeneratedTwinScan
