import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18819)) 354156589 354189357 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 354156589 354189357).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18819 354156589 354189357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18820)) 354189357 354222125 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 354189357 354222125).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18820 354189357 354222125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18821)) 354222125 354254893 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 354222125 354254893).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18821 354222125 354254893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18822)) 354254893 354287661 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 354254893 354287661).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18822 354254893 354287661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 354156589 354222125).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 354156589 ≤ 354189357)
    (by decide : 354189357 ≤ 354222125) block0 block1

theorem join_0_1 : (twinPrimeSegment 354222125 354287661).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 354222125 ≤ 354254893)
    (by decide : 354254893 ≤ 354287661) block2 block3

theorem join_1_0 : (twinPrimeSegment 354156589 354287661).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 354156589 ≤ 354222125)
    (by decide : 354222125 ≤ 354287661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 354156589 354287661).card = 451 := join_1_0

end S168C14
end Sude.GeneratedTwinScan
