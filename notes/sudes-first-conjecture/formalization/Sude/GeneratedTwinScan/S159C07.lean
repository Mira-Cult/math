import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18286)) 334364717 334397485 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334364717 334397485).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18286 334364717 334397485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18287)) 334397485 334430253 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334397485 334430253).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18287 334397485 334430253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18288)) 334430253 334463021 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334430253 334463021).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18288 334430253 334463021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18289)) 334463021 334495789 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334463021 334495789).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18289 334463021 334495789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334364717 334430253).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 334364717 ≤ 334397485)
    (by decide : 334397485 ≤ 334430253) block0 block1

theorem join_0_1 : (twinPrimeSegment 334430253 334495789).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 334430253 ≤ 334463021)
    (by decide : 334463021 ≤ 334495789) block2 block3

theorem join_1_0 : (twinPrimeSegment 334364717 334495789).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 334364717 ≤ 334430253)
    (by decide : 334430253 ≤ 334495789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334364717 334495789).card = 481 := join_1_0

end S159C07
end Sude.GeneratedTwinScan
