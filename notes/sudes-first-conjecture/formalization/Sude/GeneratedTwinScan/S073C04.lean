import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12395)) 153616429 153649197 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153616429 153649197).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12395 153616429 153649197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12396)) 153649197 153681965 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153649197 153681965).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12396 153649197 153681965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12398)) 153681965 153714733 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153681965 153714733).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12398 153681965 153714733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12399)) 153714733 153747501 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153714733 153747501).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12399 153714733 153747501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153616429 153681965).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 153616429 ≤ 153649197)
    (by decide : 153649197 ≤ 153681965) block0 block1

theorem join_0_1 : (twinPrimeSegment 153681965 153747501).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 153681965 ≤ 153714733)
    (by decide : 153714733 ≤ 153747501) block2 block3

theorem join_1_0 : (twinPrimeSegment 153616429 153747501).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 153616429 ≤ 153681965)
    (by decide : 153681965 ≤ 153747501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153616429 153747501).card = 474 := join_1_0

end S073C04
end Sude.GeneratedTwinScan
