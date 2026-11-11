import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17116)) 292945965 292978733 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292945965 292978733).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17116 292945965 292978733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17117)) 292978733 293011501 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292978733 293011501).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17117 292978733 293011501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17118)) 293011501 293044269 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 293011501 293044269).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17118 293011501 293044269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17119)) 293044269 293077037 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 293044269 293077037).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17119 293044269 293077037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292945965 293011501).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 292945965 ≤ 292978733)
    (by decide : 292978733 ≤ 293011501) block0 block1

theorem join_0_1 : (twinPrimeSegment 293011501 293077037).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 293011501 ≤ 293044269)
    (by decide : 293044269 ≤ 293077037) block2 block3

theorem join_1_0 : (twinPrimeSegment 292945965 293077037).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 292945965 ≤ 293011501)
    (by decide : 293011501 ≤ 293077037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292945965 293077037).card = 468 := join_1_0

end S139C11
end Sude.GeneratedTwinScan
