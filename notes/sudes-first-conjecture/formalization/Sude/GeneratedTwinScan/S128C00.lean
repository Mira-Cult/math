import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16385)) 268435501 268468269 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 268435501 268468269).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16385 268435501 268468269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16386)) 268468269 268501037 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 268468269 268501037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16386 268468269 268501037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16387)) 268501037 268533805 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 268501037 268533805).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16387 268501037 268533805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16388)) 268533805 268566573 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 268533805 268566573).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16388 268533805 268566573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 268435501 268501037).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 268468269)
    (by decide : 268468269 ≤ 268501037) block0 block1

theorem join_0_1 : (twinPrimeSegment 268501037 268566573).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 268501037 ≤ 268533805)
    (by decide : 268533805 ≤ 268566573) block2 block3

theorem join_1_0 : (twinPrimeSegment 268435501 268566573).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 268435501 ≤ 268501037)
    (by decide : 268501037 ≤ 268566573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 268435501 268566573).card = 475 := join_1_0

end S128C00
end Sude.GeneratedTwinScan
