import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18697)) 349569069 349601837 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349569069 349601837).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18697 349569069 349601837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18698)) 349601837 349634605 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349601837 349634605).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18698 349601837 349634605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18699)) 349634605 349667373 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 349634605 349667373).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18699 349634605 349667373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18700)) 349667373 349700141 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 349667373 349700141).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18700 349667373 349700141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349569069 349634605).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 349569069 ≤ 349601837)
    (by decide : 349601837 ≤ 349634605) block0 block1

theorem join_0_1 : (twinPrimeSegment 349634605 349700141).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 349634605 ≤ 349667373)
    (by decide : 349667373 ≤ 349700141) block2 block3

theorem join_1_0 : (twinPrimeSegment 349569069 349700141).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 349569069 ≤ 349634605)
    (by decide : 349634605 ≤ 349700141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349569069 349700141).card = 450 := join_1_0

end S166C11
end Sude.GeneratedTwinScan
