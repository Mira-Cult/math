import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18404)) 338690093 338722861 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338690093 338722861).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18404 338690093 338722861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18405)) 338722861 338755629 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338722861 338755629).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18405 338722861 338755629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18406)) 338755629 338788397 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 338755629 338788397).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18406 338755629 338788397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18407)) 338788397 338821165 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338788397 338821165).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18407 338788397 338821165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338690093 338755629).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 338690093 ≤ 338722861)
    (by decide : 338722861 ≤ 338755629) block0 block1

theorem join_0_1 : (twinPrimeSegment 338755629 338821165).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 338755629 ≤ 338788397)
    (by decide : 338788397 ≤ 338821165) block2 block3

theorem join_1_0 : (twinPrimeSegment 338690093 338821165).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 338690093 ≤ 338755629)
    (by decide : 338755629 ≤ 338821165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338690093 338821165).card = 430 := join_1_0

end S161C08
end Sude.GeneratedTwinScan
