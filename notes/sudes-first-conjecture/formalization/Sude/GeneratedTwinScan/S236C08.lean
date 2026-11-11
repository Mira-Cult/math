import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S236C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22271)) 495976493 496009261 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 495976493 496009261).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22271 495976493 496009261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22272)) 496009261 496042029 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 496009261 496042029).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22272 496009261 496042029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22272)) 496042029 496074797 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 496042029 496074797).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22272 496042029 496074797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22273)) 496074797 496107565 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 496074797 496107565).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22273 496074797 496107565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 495976493 496042029).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 495976493 ≤ 496009261)
    (by decide : 496009261 ≤ 496042029) block0 block1

theorem join_0_1 : (twinPrimeSegment 496042029 496107565).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 496042029 ≤ 496074797)
    (by decide : 496074797 ≤ 496107565) block2 block3

theorem join_1_0 : (twinPrimeSegment 495976493 496107565).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 495976493 ≤ 496042029)
    (by decide : 496042029 ≤ 496107565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 495976493 496107565).card = 436 := join_1_0

end S236C08
end Sude.GeneratedTwinScan
