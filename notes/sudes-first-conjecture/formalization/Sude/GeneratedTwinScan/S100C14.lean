import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14545)) 211550253 211583021 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211550253 211583021).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14545 211550253 211583021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14547)) 211583021 211615789 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211583021 211615789).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14547 211583021 211615789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14548)) 211615789 211648557 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 211615789 211648557).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14548 211615789 211648557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14549)) 211648557 211681325 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 211648557 211681325).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14549 211648557 211681325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211550253 211615789).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 211550253 ≤ 211583021)
    (by decide : 211583021 ≤ 211615789) block0 block1

theorem join_0_1 : (twinPrimeSegment 211615789 211681325).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 211615789 ≤ 211648557)
    (by decide : 211648557 ≤ 211681325) block2 block3

theorem join_1_0 : (twinPrimeSegment 211550253 211681325).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 211550253 ≤ 211615789)
    (by decide : 211615789 ≤ 211681325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211550253 211681325).card = 497 := join_1_0

end S100C14
end Sude.GeneratedTwinScan
