import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14831)) 219938861 219971629 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 219938861 219971629).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14831 219938861 219971629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14832)) 219971629 220004397 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 219971629 220004397).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14832 219971629 220004397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14833)) 220004397 220037165 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220004397 220037165).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14833 220004397 220037165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14834)) 220037165 220069933 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220037165 220069933).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14834 220037165 220069933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 219938861 220004397).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 219938861 ≤ 219971629)
    (by decide : 219971629 ≤ 220004397) block0 block1

theorem join_0_1 : (twinPrimeSegment 220004397 220069933).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 220004397 ≤ 220037165)
    (by decide : 220037165 ≤ 220069933) block2 block3

theorem join_1_0 : (twinPrimeSegment 219938861 220069933).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 219938861 ≤ 220004397)
    (by decide : 220004397 ≤ 220069933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 219938861 220069933).card = 466 := join_1_0

end S104C14
end Sude.GeneratedTwinScan
