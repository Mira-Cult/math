import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20706)) 428736557 428769325 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 428736557 428769325).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20706 428736557 428769325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20707)) 428769325 428802093 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 428769325 428802093).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20707 428769325 428802093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20708)) 428802093 428834861 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428802093 428834861).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20708 428802093 428834861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20709)) 428834861 428867629 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428834861 428867629).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20709 428834861 428867629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 428736557 428802093).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 428736557 ≤ 428769325)
    (by decide : 428769325 ≤ 428802093) block0 block1

theorem join_0_1 : (twinPrimeSegment 428802093 428867629).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 428802093 ≤ 428834861)
    (by decide : 428834861 ≤ 428867629) block2 block3

theorem join_1_0 : (twinPrimeSegment 428736557 428867629).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 428736557 ≤ 428802093)
    (by decide : 428802093 ≤ 428867629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 428736557 428867629).card = 435 := join_1_0

end S204C07
end Sude.GeneratedTwinScan
