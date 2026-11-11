import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13450)) 180879405 180912173 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 180879405 180912173).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13450 180879405 180912173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13451)) 180912173 180944941 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 180912173 180944941).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13451 180912173 180944941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13452)) 180944941 180977709 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 180944941 180977709).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13452 180944941 180977709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13454)) 180977709 181010477 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 180977709 181010477).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13454 180977709 181010477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 180879405 180944941).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 180879405 ≤ 180912173)
    (by decide : 180912173 ≤ 180944941) block0 block1

theorem join_0_1 : (twinPrimeSegment 180944941 181010477).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 180944941 ≤ 180977709)
    (by decide : 180977709 ≤ 181010477) block2 block3

theorem join_1_0 : (twinPrimeSegment 180879405 181010477).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 180879405 ≤ 180944941)
    (by decide : 180944941 ≤ 181010477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 180879405 181010477).card = 452 := join_1_0

end S086C04
end Sude.GeneratedTwinScan
