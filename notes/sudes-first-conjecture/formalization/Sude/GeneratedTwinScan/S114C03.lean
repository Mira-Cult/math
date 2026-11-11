import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S114C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15475)) 239468589 239501357 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 239468589 239501357).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15475 239468589 239501357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15476)) 239501357 239534125 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 239501357 239534125).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15476 239501357 239534125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15477)) 239534125 239566893 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 239534125 239566893).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15477 239534125 239566893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15479)) 239566893 239599661 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 239566893 239599661).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15479 239566893 239599661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 239468589 239534125).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 239468589 ≤ 239501357)
    (by decide : 239501357 ≤ 239534125) block0 block1

theorem join_0_1 : (twinPrimeSegment 239534125 239599661).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 239534125 ≤ 239566893)
    (by decide : 239566893 ≤ 239599661) block2 block3

theorem join_1_0 : (twinPrimeSegment 239468589 239599661).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 239468589 ≤ 239534125)
    (by decide : 239534125 ≤ 239599661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 239468589 239599661).card = 483 := join_1_0

end S114C03
end Sude.GeneratedTwinScan
