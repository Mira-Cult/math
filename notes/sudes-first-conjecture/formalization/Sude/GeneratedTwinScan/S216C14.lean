import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21327)) 454819885 454852653 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 454819885 454852653).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21327 454819885 454852653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21328)) 454852653 454885421 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 454852653 454885421).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21328 454852653 454885421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21328)) 454885421 454918189 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 454885421 454918189).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21328 454885421 454918189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21329)) 454918189 454950957 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 454918189 454950957).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21329 454918189 454950957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 454819885 454885421).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 454819885 ≤ 454852653)
    (by decide : 454852653 ≤ 454885421) block0 block1

theorem join_0_1 : (twinPrimeSegment 454885421 454950957).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 454885421 ≤ 454918189)
    (by decide : 454918189 ≤ 454950957) block2 block3

theorem join_1_0 : (twinPrimeSegment 454819885 454950957).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 454819885 ≤ 454885421)
    (by decide : 454885421 ≤ 454950957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 454819885 454950957).card = 452 := join_1_0

end S216C14
end Sude.GeneratedTwinScan
