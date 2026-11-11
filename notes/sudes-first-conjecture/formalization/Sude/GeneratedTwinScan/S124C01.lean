import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16131)) 260177965 260210733 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260177965 260210733).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16131 260177965 260210733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16132)) 260210733 260243501 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260210733 260243501).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16132 260210733 260243501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16133)) 260243501 260276269 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260243501 260276269).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16133 260243501 260276269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16134)) 260276269 260309037 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260276269 260309037).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16134 260276269 260309037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260177965 260243501).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 260177965 ≤ 260210733)
    (by decide : 260210733 ≤ 260243501) block0 block1

theorem join_0_1 : (twinPrimeSegment 260243501 260309037).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 260243501 ≤ 260276269)
    (by decide : 260276269 ≤ 260309037) block2 block3

theorem join_1_0 : (twinPrimeSegment 260177965 260309037).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 260177965 ≤ 260243501)
    (by decide : 260243501 ≤ 260309037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260177965 260309037).card = 467 := join_1_0

end S124C01
end Sude.GeneratedTwinScan
