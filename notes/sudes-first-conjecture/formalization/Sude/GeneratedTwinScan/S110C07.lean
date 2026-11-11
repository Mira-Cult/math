import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15219)) 231604269 231637037 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 231604269 231637037).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15219 231604269 231637037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15220)) 231637037 231669805 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 231637037 231669805).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15220 231637037 231669805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15221)) 231669805 231702573 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 231669805 231702573).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15221 231669805 231702573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15222)) 231702573 231735341 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 231702573 231735341).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15222 231702573 231735341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 231604269 231669805).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 231604269 ≤ 231637037)
    (by decide : 231637037 ≤ 231669805) block0 block1

theorem join_0_1 : (twinPrimeSegment 231669805 231735341).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 231669805 ≤ 231702573)
    (by decide : 231702573 ≤ 231735341) block2 block3

theorem join_1_0 : (twinPrimeSegment 231604269 231735341).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 231604269 ≤ 231669805)
    (by decide : 231669805 ≤ 231735341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 231604269 231735341).card = 455 := join_1_0

end S110C07
end Sude.GeneratedTwinScan
