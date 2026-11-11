import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16635)) 276693037 276725805 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276693037 276725805).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16635 276693037 276725805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16636)) 276725805 276758573 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276725805 276758573).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16636 276725805 276758573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16637)) 276758573 276791341 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 276758573 276791341).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16637 276758573 276791341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16638)) 276791341 276824109 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 276791341 276824109).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16638 276791341 276824109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276693037 276758573).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 276693037 ≤ 276725805)
    (by decide : 276725805 ≤ 276758573) block0 block1

theorem join_0_1 : (twinPrimeSegment 276758573 276824109).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 276758573 ≤ 276791341)
    (by decide : 276791341 ≤ 276824109) block2 block3

theorem join_1_0 : (twinPrimeSegment 276693037 276824109).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 276693037 ≤ 276758573)
    (by decide : 276758573 ≤ 276824109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276693037 276824109).card = 489 := join_1_0

end S131C15
end Sude.GeneratedTwinScan
