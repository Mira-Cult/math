import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21367)) 456523821 456556589 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456523821 456556589).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21367 456523821 456556589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21367)) 456556589 456589357 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456556589 456589357).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21367 456556589 456589357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21368)) 456589357 456622125 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456589357 456622125).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21368 456589357 456622125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21369)) 456622125 456654893 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 456622125 456654893).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21369 456622125 456654893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456523821 456589357).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 456523821 ≤ 456556589)
    (by decide : 456556589 ≤ 456589357) block0 block1

theorem join_0_1 : (twinPrimeSegment 456589357 456654893).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 456589357 ≤ 456622125)
    (by decide : 456622125 ≤ 456654893) block2 block3

theorem join_1_0 : (twinPrimeSegment 456523821 456654893).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 456523821 ≤ 456589357)
    (by decide : 456589357 ≤ 456654893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456523821 456654893).card = 443 := join_1_0

end S217C11
end Sude.GeneratedTwinScan
