import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19664)) 386662445 386695213 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386662445 386695213).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19664 386662445 386695213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19665)) 386695213 386727981 = 94 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386695213 386727981).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19665 386695213 386727981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19666)) 386727981 386760749 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386727981 386760749).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19666 386727981 386760749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19667)) 386760749 386793517 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386760749 386793517).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19667 386760749 386793517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386662445 386727981).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 386662445 ≤ 386695213)
    (by decide : 386695213 ≤ 386727981) block0 block1

theorem join_0_1 : (twinPrimeSegment 386727981 386793517).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 386727981 ≤ 386760749)
    (by decide : 386760749 ≤ 386793517) block2 block3

theorem join_1_0 : (twinPrimeSegment 386662445 386793517).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 386662445 ≤ 386727981)
    (by decide : 386727981 ≤ 386793517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386662445 386793517).card = 401 := join_1_0

end S184C06
end Sude.GeneratedTwinScan
