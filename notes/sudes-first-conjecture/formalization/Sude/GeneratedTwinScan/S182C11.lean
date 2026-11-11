import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19574)) 383123501 383156269 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 383123501 383156269).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19574 383123501 383156269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19575)) 383156269 383189037 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 383156269 383189037).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19575 383156269 383189037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19576)) 383189037 383221805 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 383189037 383221805).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19576 383189037 383221805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19576)) 383221805 383254573 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 383221805 383254573).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19576 383221805 383254573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 383123501 383189037).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 383123501 ≤ 383156269)
    (by decide : 383156269 ≤ 383189037) block0 block1

theorem join_0_1 : (twinPrimeSegment 383189037 383254573).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 383189037 ≤ 383221805)
    (by decide : 383221805 ≤ 383254573) block2 block3

theorem join_1_0 : (twinPrimeSegment 383123501 383254573).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 383123501 ≤ 383189037)
    (by decide : 383189037 ≤ 383254573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 383123501 383254573).card = 450 := join_1_0

end S182C11
end Sude.GeneratedTwinScan
