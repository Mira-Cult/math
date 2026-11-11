import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19041)) 362545197 362577965 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362545197 362577965).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19041 362545197 362577965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19042)) 362577965 362610733 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362577965 362610733).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19042 362577965 362610733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19043)) 362610733 362643501 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362610733 362643501).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19043 362610733 362643501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19044)) 362643501 362676269 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362643501 362676269).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19044 362643501 362676269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362545197 362610733).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 362545197 ≤ 362577965)
    (by decide : 362577965 ≤ 362610733) block0 block1

theorem join_0_1 : (twinPrimeSegment 362610733 362676269).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 362610733 ≤ 362643501)
    (by decide : 362643501 ≤ 362676269) block2 block3

theorem join_1_0 : (twinPrimeSegment 362545197 362676269).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 362545197 ≤ 362610733)
    (by decide : 362610733 ≤ 362676269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362545197 362676269).card = 454 := join_1_0

end S172C14
end Sude.GeneratedTwinScan
