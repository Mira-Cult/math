import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18048)) 325713965 325746733 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325713965 325746733).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18048 325713965 325746733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18049)) 325746733 325779501 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 325746733 325779501).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18049 325746733 325779501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18050)) 325779501 325812269 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 325779501 325812269).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18050 325779501 325812269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18051)) 325812269 325845037 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325812269 325845037).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18051 325812269 325845037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325713965 325779501).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 325713965 ≤ 325746733)
    (by decide : 325746733 ≤ 325779501) block0 block1

theorem join_0_1 : (twinPrimeSegment 325779501 325845037).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 325779501 ≤ 325812269)
    (by decide : 325812269 ≤ 325845037) block2 block3

theorem join_1_0 : (twinPrimeSegment 325713965 325845037).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 325713965 ≤ 325779501)
    (by decide : 325779501 ≤ 325845037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325713965 325845037).card = 420 := join_1_0

end S155C05
end Sude.GeneratedTwinScan
