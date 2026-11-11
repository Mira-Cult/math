import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19017)) 361627693 361660461 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 361627693 361660461).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19017 361627693 361660461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19018)) 361660461 361693229 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 361660461 361693229).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19018 361660461 361693229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19019)) 361693229 361725997 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 361693229 361725997).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19019 361693229 361725997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19019)) 361725997 361758765 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 361725997 361758765).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19019 361725997 361758765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 361627693 361693229).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 361627693 ≤ 361660461)
    (by decide : 361660461 ≤ 361693229) block0 block1

theorem join_0_1 : (twinPrimeSegment 361693229 361758765).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 361693229 ≤ 361725997)
    (by decide : 361725997 ≤ 361758765) block2 block3

theorem join_1_0 : (twinPrimeSegment 361627693 361758765).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 361627693 ≤ 361693229)
    (by decide : 361693229 ≤ 361758765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 361627693 361758765).card = 439 := join_1_0

end S172C07
end Sude.GeneratedTwinScan
