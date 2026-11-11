import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S218C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21425)) 459014189 459046957 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 459014189 459046957).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21425 459014189 459046957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21426)) 459046957 459079725 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 459046957 459079725).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21426 459046957 459079725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21426)) 459079725 459112493 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 459079725 459112493).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21426 459079725 459112493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21427)) 459112493 459145261 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 459112493 459145261).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21427 459112493 459145261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 459014189 459079725).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 459014189 ≤ 459046957)
    (by decide : 459046957 ≤ 459079725) block0 block1

theorem join_0_1 : (twinPrimeSegment 459079725 459145261).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 459079725 ≤ 459112493)
    (by decide : 459112493 ≤ 459145261) block2 block3

theorem join_1_0 : (twinPrimeSegment 459014189 459145261).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 459014189 ≤ 459079725)
    (by decide : 459079725 ≤ 459145261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 459014189 459145261).card = 472 := join_1_0

end S218C14
end Sude.GeneratedTwinScan
