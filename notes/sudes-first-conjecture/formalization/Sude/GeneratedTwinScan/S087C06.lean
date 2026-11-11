import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S087C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13537)) 183238701 183271469 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 183238701 183271469).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13537 183238701 183271469
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13538)) 183271469 183304237 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 183271469 183304237).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13538 183271469 183304237
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13540)) 183304237 183337005 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 183304237 183337005).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13540 183304237 183337005
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13541)) 183337005 183369773 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 183337005 183369773).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13541 183337005 183369773
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 183238701 183304237).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 183238701 ≤ 183271469)
    (by decide : 183271469 ≤ 183304237) block0 block1

theorem join_0_1 : (twinPrimeSegment 183304237 183369773).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 183304237 ≤ 183337005)
    (by decide : 183337005 ≤ 183369773) block2 block3

theorem join_1_0 : (twinPrimeSegment 183238701 183369773).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 183238701 ≤ 183304237)
    (by decide : 183304237 ≤ 183369773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 183238701 183369773).card = 465 := join_1_0

end S087C06
end Sude.GeneratedTwinScan
