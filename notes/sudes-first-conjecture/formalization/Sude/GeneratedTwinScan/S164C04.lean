import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18560)) 344457261 344490029 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344457261 344490029).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18560 344457261 344490029
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18561)) 344490029 344522797 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344490029 344522797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18561 344490029 344522797
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18562)) 344522797 344555565 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344522797 344555565).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18562 344522797 344555565
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18563)) 344555565 344588333 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344555565 344588333).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18563 344555565 344588333
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344457261 344522797).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 344457261 ≤ 344490029)
    (by decide : 344490029 ≤ 344522797) block0 block1

theorem join_0_1 : (twinPrimeSegment 344522797 344588333).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 344522797 ≤ 344555565)
    (by decide : 344555565 ≤ 344588333) block2 block3

theorem join_1_0 : (twinPrimeSegment 344457261 344588333).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 344457261 ≤ 344522797)
    (by decide : 344522797 ≤ 344588333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344457261 344588333).card = 461 := join_1_0

end S164C04
end Sude.GeneratedTwinScan
