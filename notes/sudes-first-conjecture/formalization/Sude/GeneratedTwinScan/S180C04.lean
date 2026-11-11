import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19443)) 378011693 378044461 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 378011693 378044461).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19443 378011693 378044461
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19444)) 378044461 378077229 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 378044461 378077229).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19444 378044461 378077229
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19445)) 378077229 378109997 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 378077229 378109997).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19445 378077229 378109997
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19445)) 378109997 378142765 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 378109997 378142765).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19445 378109997 378142765
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 378011693 378077229).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 378011693 ≤ 378044461)
    (by decide : 378044461 ≤ 378077229) block0 block1

theorem join_0_1 : (twinPrimeSegment 378077229 378142765).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 378077229 ≤ 378109997)
    (by decide : 378109997 ≤ 378142765) block2 block3

theorem join_1_0 : (twinPrimeSegment 378011693 378142765).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 378011693 ≤ 378077229)
    (by decide : 378077229 ≤ 378142765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 378011693 378142765).card = 459 := join_1_0

end S180C04
end Sude.GeneratedTwinScan
