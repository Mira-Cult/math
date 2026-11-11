import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18588)) 345505837 345538605 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 345505837 345538605).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18588 345505837 345538605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18589)) 345538605 345571373 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 345538605 345571373).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18589 345538605 345571373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18590)) 345571373 345604141 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 345571373 345604141).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18590 345571373 345604141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18591)) 345604141 345636909 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 345604141 345636909).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18591 345604141 345636909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 345505837 345571373).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 345505837 ≤ 345538605)
    (by decide : 345538605 ≤ 345571373) block0 block1

theorem join_0_1 : (twinPrimeSegment 345571373 345636909).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 345571373 ≤ 345604141)
    (by decide : 345604141 ≤ 345636909) block2 block3

theorem join_1_0 : (twinPrimeSegment 345505837 345636909).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 345505837 ≤ 345571373)
    (by decide : 345571373 ≤ 345636909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 345505837 345636909).card = 433 := join_1_0

end S164C12
end Sude.GeneratedTwinScan
