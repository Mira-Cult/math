import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16623)) 276299821 276332589 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276299821 276332589).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16623 276299821 276332589
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16624)) 276332589 276365357 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276332589 276365357).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16624 276332589 276365357
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16625)) 276365357 276398125 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 276365357 276398125).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16625 276365357 276398125
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16626)) 276398125 276430893 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276398125 276430893).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16626 276398125 276430893
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276299821 276365357).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 276299821 ≤ 276332589)
    (by decide : 276332589 ≤ 276365357) block0 block1

theorem join_0_1 : (twinPrimeSegment 276365357 276430893).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 276365357 ≤ 276398125)
    (by decide : 276398125 ≤ 276430893) block2 block3

theorem join_1_0 : (twinPrimeSegment 276299821 276430893).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 276299821 ≤ 276365357)
    (by decide : 276365357 ≤ 276430893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276299821 276430893).card = 444 := join_1_0

end S131C12
end Sude.GeneratedTwinScan
