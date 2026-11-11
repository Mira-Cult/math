import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13952)) 194641965 194674733 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 194641965 194674733).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13952 194641965 194674733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13953)) 194674733 194707501 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194674733 194707501).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13953 194674733 194707501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13954)) 194707501 194740269 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194707501 194740269).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13954 194707501 194740269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13956)) 194740269 194773037 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194740269 194773037).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13956 194740269 194773037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 194641965 194707501).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 194641965 ≤ 194674733)
    (by decide : 194674733 ≤ 194707501) block0 block1

theorem join_0_1 : (twinPrimeSegment 194707501 194773037).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 194707501 ≤ 194740269)
    (by decide : 194740269 ≤ 194773037) block2 block3

theorem join_1_0 : (twinPrimeSegment 194641965 194773037).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 194641965 ≤ 194707501)
    (by decide : 194707501 ≤ 194773037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 194641965 194773037).card = 463 := join_1_0

end S092C13
end Sude.GeneratedTwinScan
