import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22676)) 514195501 514228269 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514195501 514228269).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22676 514195501 514228269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22677)) 514228269 514261037 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514228269 514261037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22677 514228269 514261037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22678)) 514261037 514293805 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514261037 514293805).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22678 514261037 514293805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22678)) 514293805 514326573 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514293805 514326573).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22678 514293805 514326573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514195501 514261037).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 514195501 ≤ 514228269)
    (by decide : 514228269 ≤ 514261037) block0 block1

theorem join_0_1 : (twinPrimeSegment 514261037 514326573).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 514261037 ≤ 514293805)
    (by decide : 514293805 ≤ 514326573) block2 block3

theorem join_1_0 : (twinPrimeSegment 514195501 514326573).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 514195501 ≤ 514261037)
    (by decide : 514261037 ≤ 514326573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514195501 514326573).card = 440 := join_1_0

end S245C03
end Sude.GeneratedTwinScan
