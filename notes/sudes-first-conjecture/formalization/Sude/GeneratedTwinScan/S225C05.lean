import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21738)) 472514605 472547373 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472514605 472547373).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21738 472514605 472547373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21738)) 472547373 472580141 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472547373 472580141).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21738 472547373 472580141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21739)) 472580141 472612909 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472580141 472612909).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21739 472580141 472612909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21740)) 472612909 472645677 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472612909 472645677).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21740 472612909 472645677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472514605 472580141).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 472514605 ≤ 472547373)
    (by decide : 472547373 ≤ 472580141) block0 block1

theorem join_0_1 : (twinPrimeSegment 472580141 472645677).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 472580141 ≤ 472612909)
    (by decide : 472612909 ≤ 472645677) block2 block3

theorem join_1_0 : (twinPrimeSegment 472514605 472645677).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 472514605 ≤ 472580141)
    (by decide : 472580141 ≤ 472645677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472514605 472645677).card = 434 := join_1_0

end S225C05
end Sude.GeneratedTwinScan
