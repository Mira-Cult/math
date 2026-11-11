import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17629)) 310771757 310804525 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 310771757 310804525).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17629 310771757 310804525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17630)) 310804525 310837293 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 310804525 310837293).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17630 310804525 310837293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17631)) 310837293 310870061 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 310837293 310870061).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17631 310837293 310870061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17632)) 310870061 310902829 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 310870061 310902829).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17632 310870061 310902829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 310771757 310837293).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 310771757 ≤ 310804525)
    (by decide : 310804525 ≤ 310837293) block0 block1

theorem join_0_1 : (twinPrimeSegment 310837293 310902829).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 310837293 ≤ 310870061)
    (by decide : 310870061 ≤ 310902829) block2 block3

theorem join_1_0 : (twinPrimeSegment 310771757 310902829).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 310771757 ≤ 310837293)
    (by decide : 310837293 ≤ 310902829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 310771757 310902829).card = 440 := join_1_0

end S148C03
end Sude.GeneratedTwinScan
