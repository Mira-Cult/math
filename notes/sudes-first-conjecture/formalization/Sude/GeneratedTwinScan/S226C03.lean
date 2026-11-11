import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21780)) 474349613 474382381 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474349613 474382381).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21780 474349613 474382381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21781)) 474382381 474415149 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474382381 474415149).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21781 474382381 474415149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21781)) 474415149 474447917 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474415149 474447917).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21781 474415149 474447917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21782)) 474447917 474480685 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474447917 474480685).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21782 474447917 474480685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474349613 474415149).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 474349613 ≤ 474382381)
    (by decide : 474382381 ≤ 474415149) block0 block1

theorem join_0_1 : (twinPrimeSegment 474415149 474480685).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 474415149 ≤ 474447917)
    (by decide : 474447917 ≤ 474480685) block2 block3

theorem join_1_0 : (twinPrimeSegment 474349613 474480685).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 474349613 ≤ 474415149)
    (by decide : 474415149 ≤ 474480685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474349613 474480685).card = 415 := join_1_0

end S226C03
end Sude.GeneratedTwinScan
