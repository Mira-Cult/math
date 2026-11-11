import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17177)) 295043117 295075885 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295043117 295075885).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17177 295043117 295075885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17178)) 295075885 295108653 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295075885 295108653).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17178 295075885 295108653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17179)) 295108653 295141421 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 295108653 295141421).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17179 295108653 295141421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17180)) 295141421 295174189 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295141421 295174189).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17180 295141421 295174189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295043117 295108653).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 295043117 ≤ 295075885)
    (by decide : 295075885 ≤ 295108653) block0 block1

theorem join_0_1 : (twinPrimeSegment 295108653 295174189).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 295108653 ≤ 295141421)
    (by decide : 295141421 ≤ 295174189) block2 block3

theorem join_1_0 : (twinPrimeSegment 295043117 295174189).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 295043117 ≤ 295108653)
    (by decide : 295108653 ≤ 295174189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295043117 295174189).card = 433 := join_1_0

end S140C11
end Sude.GeneratedTwinScan
