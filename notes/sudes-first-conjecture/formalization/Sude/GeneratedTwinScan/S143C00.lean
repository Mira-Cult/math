import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17318)) 299892781 299925549 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 299892781 299925549).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17318 299892781 299925549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17319)) 299925549 299958317 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 299925549 299958317).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17319 299925549 299958317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17320)) 299958317 299991085 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 299958317 299991085).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17320 299958317 299991085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17321)) 299991085 300023853 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 299991085 300023853).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17321 299991085 300023853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 299892781 299958317).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 299892781 ≤ 299925549)
    (by decide : 299925549 ≤ 299958317) block0 block1

theorem join_0_1 : (twinPrimeSegment 299958317 300023853).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 299958317 ≤ 299991085)
    (by decide : 299991085 ≤ 300023853) block2 block3

theorem join_1_0 : (twinPrimeSegment 299892781 300023853).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 299892781 ≤ 299958317)
    (by decide : 299958317 ≤ 300023853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 299892781 300023853).card = 459 := join_1_0

end S143C00
end Sude.GeneratedTwinScan
