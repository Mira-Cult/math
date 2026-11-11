import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18358)) 336986157 337018925 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336986157 337018925).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18358 336986157 337018925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18358)) 337018925 337051693 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337018925 337051693).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18358 337018925 337051693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18359)) 337051693 337084461 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337051693 337084461).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18359 337051693 337084461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18360)) 337084461 337117229 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 337084461 337117229).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18360 337084461 337117229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336986157 337051693).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 336986157 ≤ 337018925)
    (by decide : 337018925 ≤ 337051693) block0 block1

theorem join_0_1 : (twinPrimeSegment 337051693 337117229).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 337051693 ≤ 337084461)
    (by decide : 337084461 ≤ 337117229) block2 block3

theorem join_1_0 : (twinPrimeSegment 336986157 337117229).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 336986157 ≤ 337051693)
    (by decide : 337051693 ≤ 337117229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336986157 337117229).card = 449 := join_1_0

end S160C11
end Sude.GeneratedTwinScan
