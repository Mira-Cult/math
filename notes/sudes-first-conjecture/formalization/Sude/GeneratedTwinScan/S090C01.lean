import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S090C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13744)) 188874797 188907565 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188874797 188907565).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13744 188874797 188907565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13745)) 188907565 188940333 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188907565 188940333).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13745 188907565 188940333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13746)) 188940333 188973101 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188940333 188973101).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13746 188940333 188973101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13747)) 188973101 189005869 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188973101 189005869).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13747 188973101 189005869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188874797 188940333).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 188874797 ≤ 188907565)
    (by decide : 188907565 ≤ 188940333) block0 block1

theorem join_0_1 : (twinPrimeSegment 188940333 189005869).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 188940333 ≤ 188973101)
    (by decide : 188973101 ≤ 189005869) block2 block3

theorem join_1_0 : (twinPrimeSegment 188874797 189005869).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 188874797 ≤ 188940333)
    (by decide : 188940333 ≤ 189005869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188874797 189005869).card = 447 := join_1_0

end S090C01
end Sude.GeneratedTwinScan
