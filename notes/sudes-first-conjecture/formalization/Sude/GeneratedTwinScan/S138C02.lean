import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17020)) 289669165 289701933 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289669165 289701933).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17020 289669165 289701933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17021)) 289701933 289734701 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289701933 289734701).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17021 289701933 289734701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17022)) 289734701 289767469 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289734701 289767469).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17022 289734701 289767469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17023)) 289767469 289800237 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 289767469 289800237).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17023 289767469 289800237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289669165 289734701).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 289669165 ≤ 289701933)
    (by decide : 289701933 ≤ 289734701) block0 block1

theorem join_0_1 : (twinPrimeSegment 289734701 289800237).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 289734701 ≤ 289767469)
    (by decide : 289767469 ≤ 289800237) block2 block3

theorem join_1_0 : (twinPrimeSegment 289669165 289800237).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 289669165 ≤ 289734701)
    (by decide : 289734701 ≤ 289800237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289669165 289800237).card = 478 := join_1_0

end S138C02
end Sude.GeneratedTwinScan
