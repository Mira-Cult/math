import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15072)) 227147821 227180589 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227147821 227180589).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15072 227147821 227180589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15073)) 227180589 227213357 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227180589 227213357).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15073 227180589 227213357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15074)) 227213357 227246125 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227213357 227246125).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15074 227213357 227246125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15075)) 227246125 227278893 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227246125 227278893).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15075 227246125 227278893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227147821 227213357).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 227147821 ≤ 227180589)
    (by decide : 227180589 ≤ 227213357) block0 block1

theorem join_0_1 : (twinPrimeSegment 227213357 227278893).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 227213357 ≤ 227246125)
    (by decide : 227246125 ≤ 227278893) block2 block3

theorem join_1_0 : (twinPrimeSegment 227147821 227278893).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 227147821 ≤ 227213357)
    (by decide : 227213357 ≤ 227278893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227147821 227278893).card = 462 := join_1_0

end S108C05
end Sude.GeneratedTwinScan
