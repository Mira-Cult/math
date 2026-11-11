import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15107)) 228196397 228229165 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228196397 228229165).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15107 228196397 228229165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15108)) 228229165 228261933 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 228229165 228261933).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15108 228229165 228261933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15109)) 228261933 228294701 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 228261933 228294701).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15109 228261933 228294701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15110)) 228294701 228327469 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228294701 228327469).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15110 228294701 228327469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228196397 228261933).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 228196397 ≤ 228229165)
    (by decide : 228229165 ≤ 228261933) block0 block1

theorem join_0_1 : (twinPrimeSegment 228261933 228327469).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 228261933 ≤ 228294701)
    (by decide : 228294701 ≤ 228327469) block2 block3

theorem join_1_0 : (twinPrimeSegment 228196397 228327469).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 228196397 ≤ 228261933)
    (by decide : 228261933 ≤ 228327469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228196397 228327469).card = 434 := join_1_0

end S108C13
end Sude.GeneratedTwinScan
