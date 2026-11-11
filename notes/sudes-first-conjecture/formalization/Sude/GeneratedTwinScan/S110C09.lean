import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15228)) 231866413 231899181 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231866413 231899181).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15228 231866413 231899181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15229)) 231899181 231931949 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231899181 231931949).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15229 231899181 231931949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15230)) 231931949 231964717 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231931949 231964717).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15230 231931949 231964717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15231)) 231964717 231997485 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231964717 231997485).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15231 231964717 231997485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231866413 231931949).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 231866413 ≤ 231899181)
    (by decide : 231899181 ≤ 231931949) block0 block1

theorem join_0_1 : (twinPrimeSegment 231931949 231997485).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 231931949 ≤ 231964717)
    (by decide : 231964717 ≤ 231997485) block2 block3

theorem join_1_0 : (twinPrimeSegment 231866413 231997485).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 231866413 ≤ 231931949)
    (by decide : 231931949 ≤ 231997485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231866413 231997485).card = 477 := join_1_0

end S110C09
end Sude.GeneratedTwinScan
