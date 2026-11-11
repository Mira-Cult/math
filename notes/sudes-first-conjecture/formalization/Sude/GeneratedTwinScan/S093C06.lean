import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13994)) 195821613 195854381 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195821613 195854381).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13994 195821613 195854381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13995)) 195854381 195887149 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195854381 195887149).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13995 195854381 195887149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13997)) 195887149 195919917 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195887149 195919917).card = 147 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13997 195887149 195919917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13998)) 195919917 195952685 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195919917 195952685).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13998 195919917 195952685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195821613 195887149).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 195821613 ≤ 195854381)
    (by decide : 195854381 ≤ 195887149) block0 block1

theorem join_0_1 : (twinPrimeSegment 195887149 195952685).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 195887149 ≤ 195919917)
    (by decide : 195919917 ≤ 195952685) block2 block3

theorem join_1_0 : (twinPrimeSegment 195821613 195952685).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 195821613 ≤ 195887149)
    (by decide : 195887149 ≤ 195952685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195821613 195952685).card = 491 := join_1_0

end S093C06
end Sude.GeneratedTwinScan
