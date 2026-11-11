import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16877)) 284819501 284852269 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284819501 284852269).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16877 284819501 284852269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16878)) 284852269 284885037 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284852269 284885037).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16878 284852269 284885037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16879)) 284885037 284917805 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284885037 284917805).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16879 284885037 284917805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16880)) 284917805 284950573 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284917805 284950573).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16880 284917805 284950573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284819501 284885037).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 284819501 ≤ 284852269)
    (by decide : 284852269 ≤ 284885037) block0 block1

theorem join_0_1 : (twinPrimeSegment 284885037 284950573).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 284885037 ≤ 284917805)
    (by decide : 284917805 ≤ 284950573) block2 block3

theorem join_1_0 : (twinPrimeSegment 284819501 284950573).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 284819501 ≤ 284885037)
    (by decide : 284885037 ≤ 284950573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284819501 284950573).card = 469 := join_1_0

end S135C13
end Sude.GeneratedTwinScan
