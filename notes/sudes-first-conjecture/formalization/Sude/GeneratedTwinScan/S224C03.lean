import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21683)) 470155309 470188077 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 470155309 470188077).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21683 470155309 470188077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21684)) 470188077 470220845 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 470188077 470220845).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21684 470188077 470220845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21685)) 470220845 470253613 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 470220845 470253613).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21685 470220845 470253613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21686)) 470253613 470286381 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 470253613 470286381).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21686 470253613 470286381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 470155309 470220845).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 470155309 ≤ 470188077)
    (by decide : 470188077 ≤ 470220845) block0 block1

theorem join_0_1 : (twinPrimeSegment 470220845 470286381).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 470220845 ≤ 470253613)
    (by decide : 470253613 ≤ 470286381) block2 block3

theorem join_1_0 : (twinPrimeSegment 470155309 470286381).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 470155309 ≤ 470220845)
    (by decide : 470220845 ≤ 470286381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 470155309 470286381).card = 433 := join_1_0

end S224C03
end Sude.GeneratedTwinScan
