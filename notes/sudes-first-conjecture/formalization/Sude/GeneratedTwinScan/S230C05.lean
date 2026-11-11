import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21978)) 483000365 483033133 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483000365 483033133).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21978 483000365 483033133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21978)) 483033133 483065901 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483033133 483065901).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21978 483033133 483065901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21979)) 483065901 483098669 = 85 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483065901 483098669).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21979 483065901 483098669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21980)) 483098669 483131437 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 483098669 483131437).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21980 483098669 483131437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483000365 483065901).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 483000365 ≤ 483033133)
    (by decide : 483033133 ≤ 483065901) block0 block1

theorem join_0_1 : (twinPrimeSegment 483065901 483131437).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 483065901 ≤ 483098669)
    (by decide : 483098669 ≤ 483131437) block2 block3

theorem join_1_0 : (twinPrimeSegment 483000365 483131437).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 483000365 ≤ 483065901)
    (by decide : 483065901 ≤ 483131437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483000365 483131437).card = 420 := join_1_0

end S230C05
end Sude.GeneratedTwinScan
