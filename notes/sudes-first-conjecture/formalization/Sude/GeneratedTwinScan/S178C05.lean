import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19338)) 373948461 373981229 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373948461 373981229).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19338 373948461 373981229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19339)) 373981229 374013997 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373981229 374013997).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19339 373981229 374013997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19340)) 374013997 374046765 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374013997 374046765).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19340 374013997 374046765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19341)) 374046765 374079533 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374046765 374079533).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19341 374046765 374079533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373948461 374013997).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 373948461 ≤ 373981229)
    (by decide : 373981229 ≤ 374013997) block0 block1

theorem join_0_1 : (twinPrimeSegment 374013997 374079533).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 374013997 ≤ 374046765)
    (by decide : 374046765 ≤ 374079533) block2 block3

theorem join_1_0 : (twinPrimeSegment 373948461 374079533).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 373948461 ≤ 374013997)
    (by decide : 374013997 ≤ 374079533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373948461 374079533).card = 434 := join_1_0

end S178C05
end Sude.GeneratedTwinScan
