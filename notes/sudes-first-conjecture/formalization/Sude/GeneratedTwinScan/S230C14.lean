import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22004)) 484180013 484212781 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484180013 484212781).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22004 484180013 484212781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22005)) 484212781 484245549 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484212781 484245549).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22005 484212781 484245549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22006)) 484245549 484278317 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484245549 484278317).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22006 484245549 484278317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22007)) 484278317 484311085 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484278317 484311085).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22007 484278317 484311085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484180013 484245549).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 484180013 ≤ 484212781)
    (by decide : 484212781 ≤ 484245549) block0 block1

theorem join_0_1 : (twinPrimeSegment 484245549 484311085).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 484245549 ≤ 484278317)
    (by decide : 484278317 ≤ 484311085) block2 block3

theorem join_1_0 : (twinPrimeSegment 484180013 484311085).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 484180013 ≤ 484245549)
    (by decide : 484245549 ≤ 484311085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484180013 484311085).card = 436 := join_1_0

end S230C14
end Sude.GeneratedTwinScan
