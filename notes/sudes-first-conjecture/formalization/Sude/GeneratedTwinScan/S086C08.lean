import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13469)) 181403693 181436461 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 181403693 181436461).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13469 181403693 181436461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13471)) 181436461 181469229 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 181436461 181469229).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13471 181436461 181469229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13472)) 181469229 181501997 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 181469229 181501997).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13472 181469229 181501997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13473)) 181501997 181534765 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 181501997 181534765).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13473 181501997 181534765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 181403693 181469229).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 181403693 ≤ 181436461)
    (by decide : 181436461 ≤ 181469229) block0 block1

theorem join_0_1 : (twinPrimeSegment 181469229 181534765).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 181469229 ≤ 181501997)
    (by decide : 181501997 ≤ 181534765) block2 block3

theorem join_1_0 : (twinPrimeSegment 181403693 181534765).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 181403693 ≤ 181469229)
    (by decide : 181469229 ≤ 181534765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 181403693 181534765).card = 485 := join_1_0

end S086C08
end Sude.GeneratedTwinScan
