import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20955)) 439091245 439124013 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 439091245 439124013).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20955 439091245 439124013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20956)) 439124013 439156781 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 439124013 439156781).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20956 439124013 439156781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20956)) 439156781 439189549 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 439156781 439189549).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20956 439156781 439189549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20957)) 439189549 439222317 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 439189549 439222317).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20957 439189549 439222317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 439091245 439156781).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 439091245 ≤ 439124013)
    (by decide : 439124013 ≤ 439156781) block0 block1

theorem join_0_1 : (twinPrimeSegment 439156781 439222317).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 439156781 ≤ 439189549)
    (by decide : 439189549 ≤ 439222317) block2 block3

theorem join_1_0 : (twinPrimeSegment 439091245 439222317).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 439091245 ≤ 439156781)
    (by decide : 439156781 ≤ 439222317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 439091245 439222317).card = 454 := join_1_0

end S209C06
end Sude.GeneratedTwinScan
