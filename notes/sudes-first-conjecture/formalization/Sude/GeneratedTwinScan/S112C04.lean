import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15343)) 235405357 235438125 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235405357 235438125).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15343 235405357 235438125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15345)) 235438125 235470893 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235438125 235470893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15345 235438125 235470893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15346)) 235470893 235503661 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235470893 235503661).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15346 235470893 235503661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15347)) 235503661 235536429 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 235503661 235536429).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15347 235503661 235536429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235405357 235470893).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 235405357 ≤ 235438125)
    (by decide : 235438125 ≤ 235470893) block0 block1

theorem join_0_1 : (twinPrimeSegment 235470893 235536429).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 235470893 ≤ 235503661)
    (by decide : 235503661 ≤ 235536429) block2 block3

theorem join_1_0 : (twinPrimeSegment 235405357 235536429).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 235405357 ≤ 235470893)
    (by decide : 235470893 ≤ 235536429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235405357 235536429).card = 455 := join_1_0

end S112C04
end Sude.GeneratedTwinScan
