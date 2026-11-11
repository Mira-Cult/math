import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13357)) 178389037 178421805 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 178389037 178421805).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13357 178389037 178421805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13358)) 178421805 178454573 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178421805 178454573).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13358 178421805 178454573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13359)) 178454573 178487341 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178454573 178487341).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13359 178454573 178487341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13361)) 178487341 178520109 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 178487341 178520109).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13361 178487341 178520109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 178389037 178454573).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 178389037 ≤ 178421805)
    (by decide : 178421805 ≤ 178454573) block0 block1

theorem join_0_1 : (twinPrimeSegment 178454573 178520109).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 178454573 ≤ 178487341)
    (by decide : 178487341 ≤ 178520109) block2 block3

theorem join_1_0 : (twinPrimeSegment 178389037 178520109).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 178389037 ≤ 178454573)
    (by decide : 178454573 ≤ 178520109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 178389037 178520109).card = 466 := join_1_0

end S085C01
end Sude.GeneratedTwinScan
