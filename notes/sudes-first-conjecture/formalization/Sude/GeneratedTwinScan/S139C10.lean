import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17112)) 292814893 292847661 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 292814893 292847661).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17112 292814893 292847661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17113)) 292847661 292880429 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 292847661 292880429).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17113 292847661 292880429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17114)) 292880429 292913197 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 292880429 292913197).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17114 292880429 292913197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17115)) 292913197 292945965 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 292913197 292945965).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17115 292913197 292945965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 292814893 292880429).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 292814893 ≤ 292847661)
    (by decide : 292847661 ≤ 292880429) block0 block1

theorem join_0_1 : (twinPrimeSegment 292880429 292945965).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 292880429 ≤ 292913197)
    (by decide : 292913197 ≤ 292945965) block2 block3

theorem join_1_0 : (twinPrimeSegment 292814893 292945965).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 292814893 ≤ 292880429)
    (by decide : 292880429 ≤ 292945965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 292814893 292945965).card = 450 := join_1_0

end S139C10
end Sude.GeneratedTwinScan
