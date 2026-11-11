import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20496)) 420085805 420118573 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 420085805 420118573).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20496 420085805 420118573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20497)) 420118573 420151341 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 420118573 420151341).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20497 420118573 420151341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20498)) 420151341 420184109 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 420151341 420184109).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20498 420151341 420184109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20499)) 420184109 420216877 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 420184109 420216877).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20499 420184109 420216877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 420085805 420151341).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 420085805 ≤ 420118573)
    (by decide : 420118573 ≤ 420151341) block0 block1

theorem join_0_1 : (twinPrimeSegment 420151341 420216877).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 420151341 ≤ 420184109)
    (by decide : 420184109 ≤ 420216877) block2 block3

theorem join_1_0 : (twinPrimeSegment 420085805 420216877).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 420085805 ≤ 420151341)
    (by decide : 420151341 ≤ 420216877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 420085805 420216877).card = 477 := join_1_0

end S200C05
end Sude.GeneratedTwinScan
