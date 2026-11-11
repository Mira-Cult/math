import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14391)) 207093805 207126573 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 207093805 207126573).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14391 207093805 207126573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14393)) 207126573 207159341 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 207126573 207159341).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14393 207126573 207159341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14394)) 207159341 207192109 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 207159341 207192109).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14394 207159341 207192109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14395)) 207192109 207224877 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 207192109 207224877).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14395 207192109 207224877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 207093805 207159341).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 207093805 ≤ 207126573)
    (by decide : 207126573 ≤ 207159341) block0 block1

theorem join_0_1 : (twinPrimeSegment 207159341 207224877).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 207159341 ≤ 207192109)
    (by decide : 207192109 ≤ 207224877) block2 block3

theorem join_1_0 : (twinPrimeSegment 207093805 207224877).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 207093805 ≤ 207159341)
    (by decide : 207159341 ≤ 207224877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 207093805 207224877).card = 460 := join_1_0

end S098C12
end Sude.GeneratedTwinScan
