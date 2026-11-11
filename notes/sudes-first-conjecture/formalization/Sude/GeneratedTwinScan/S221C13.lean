import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21568)) 465174573 465207341 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465174573 465207341).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21568 465174573 465207341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21569)) 465207341 465240109 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465207341 465240109).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21569 465207341 465240109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21570)) 465240109 465272877 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 465240109 465272877).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21570 465240109 465272877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21570)) 465272877 465305645 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465272877 465305645).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21570 465272877 465305645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465174573 465240109).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 465174573 ≤ 465207341)
    (by decide : 465207341 ≤ 465240109) block0 block1

theorem join_0_1 : (twinPrimeSegment 465240109 465305645).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 465240109 ≤ 465272877)
    (by decide : 465272877 ≤ 465305645) block2 block3

theorem join_1_0 : (twinPrimeSegment 465174573 465305645).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 465174573 ≤ 465240109)
    (by decide : 465240109 ≤ 465305645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465174573 465305645).card = 420 := join_1_0

end S221C13
end Sude.GeneratedTwinScan
