import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18044)) 325582893 325615661 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325582893 325615661).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18044 325582893 325615661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18045)) 325615661 325648429 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 325615661 325648429).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18045 325615661 325648429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18046)) 325648429 325681197 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 325648429 325681197).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18046 325648429 325681197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18047)) 325681197 325713965 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325681197 325713965).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18047 325681197 325713965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325582893 325648429).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 325582893 ≤ 325615661)
    (by decide : 325615661 ≤ 325648429) block0 block1

theorem join_0_1 : (twinPrimeSegment 325648429 325713965).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 325648429 ≤ 325681197)
    (by decide : 325681197 ≤ 325713965) block2 block3

theorem join_1_0 : (twinPrimeSegment 325582893 325713965).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 325582893 ≤ 325648429)
    (by decide : 325648429 ≤ 325713965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325582893 325713965).card = 468 := join_1_0

end S155C04
end Sude.GeneratedTwinScan
