import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19151)) 366739501 366772269 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366739501 366772269).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19151 366739501 366772269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19152)) 366772269 366805037 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366772269 366805037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19152 366772269 366805037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19153)) 366805037 366837805 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366805037 366837805).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19153 366805037 366837805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19153)) 366837805 366870573 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366837805 366870573).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19153 366837805 366870573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366739501 366805037).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 366739501 ≤ 366772269)
    (by decide : 366772269 ≤ 366805037) block0 block1

theorem join_0_1 : (twinPrimeSegment 366805037 366870573).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 366805037 ≤ 366837805)
    (by decide : 366837805 ≤ 366870573) block2 block3

theorem join_1_0 : (twinPrimeSegment 366739501 366870573).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 366739501 ≤ 366805037)
    (by decide : 366805037 ≤ 366870573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366739501 366870573).card = 454 := join_1_0

end S174C14
end Sude.GeneratedTwinScan
