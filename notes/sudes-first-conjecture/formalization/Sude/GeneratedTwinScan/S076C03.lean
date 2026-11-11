import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12641)) 159776813 159809581 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159776813 159809581).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12641 159776813 159809581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12642)) 159809581 159842349 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159809581 159842349).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12642 159809581 159842349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12644)) 159842349 159875117 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159842349 159875117).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12644 159842349 159875117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12645)) 159875117 159907885 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159875117 159907885).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12645 159875117 159907885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159776813 159842349).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 159776813 ≤ 159809581)
    (by decide : 159809581 ≤ 159842349) block0 block1

theorem join_0_1 : (twinPrimeSegment 159842349 159907885).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 159842349 ≤ 159875117)
    (by decide : 159875117 ≤ 159907885) block2 block3

theorem join_1_0 : (twinPrimeSegment 159776813 159907885).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 159776813 ≤ 159842349)
    (by decide : 159842349 ≤ 159907885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159776813 159907885).card = 505 := join_1_0

end S076C03
end Sude.GeneratedTwinScan
