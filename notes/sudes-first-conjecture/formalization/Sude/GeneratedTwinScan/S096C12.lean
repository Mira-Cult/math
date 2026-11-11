import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S096C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14245)) 202899501 202932269 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 202899501 202932269).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14245 202899501 202932269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14246)) 202932269 202965037 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 202932269 202965037).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14246 202932269 202965037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14247)) 202965037 202997805 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 202965037 202997805).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14247 202965037 202997805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14248)) 202997805 203030573 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 202997805 203030573).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14248 202997805 203030573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 202899501 202965037).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 202899501 ≤ 202932269)
    (by decide : 202932269 ≤ 202965037) block0 block1

theorem join_0_1 : (twinPrimeSegment 202965037 203030573).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 202965037 ≤ 202997805)
    (by decide : 202997805 ≤ 203030573) block2 block3

theorem join_1_0 : (twinPrimeSegment 202899501 203030573).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 202899501 ≤ 202965037)
    (by decide : 202965037 ≤ 203030573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 202899501 203030573).card = 497 := join_1_0

end S096C12
end Sude.GeneratedTwinScan
