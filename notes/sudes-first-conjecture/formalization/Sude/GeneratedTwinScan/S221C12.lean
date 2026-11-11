import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21565)) 465043501 465076269 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465043501 465076269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21565 465043501 465076269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21566)) 465076269 465109037 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465076269 465109037).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21566 465076269 465109037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21567)) 465109037 465141805 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 465109037 465141805).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21567 465109037 465141805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21567)) 465141805 465174573 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465141805 465174573).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21567 465141805 465174573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465043501 465109037).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 465043501 ≤ 465076269)
    (by decide : 465076269 ≤ 465109037) block0 block1

theorem join_0_1 : (twinPrimeSegment 465109037 465174573).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 465109037 ≤ 465141805)
    (by decide : 465141805 ≤ 465174573) block2 block3

theorem join_1_0 : (twinPrimeSegment 465043501 465174573).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 465043501 ≤ 465109037)
    (by decide : 465109037 ≤ 465174573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465043501 465174573).card = 446 := join_1_0

end S221C12
end Sude.GeneratedTwinScan
