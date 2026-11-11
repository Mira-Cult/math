import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18833)) 354680877 354713645 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 354680877 354713645).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18833 354680877 354713645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18834)) 354713645 354746413 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 354713645 354746413).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18834 354713645 354746413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18835)) 354746413 354779181 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 354746413 354779181).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18835 354746413 354779181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18836)) 354779181 354811949 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 354779181 354811949).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18836 354779181 354811949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 354680877 354746413).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 354680877 ≤ 354713645)
    (by decide : 354713645 ≤ 354746413) block0 block1

theorem join_0_1 : (twinPrimeSegment 354746413 354811949).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 354746413 ≤ 354779181)
    (by decide : 354779181 ≤ 354811949) block2 block3

theorem join_1_0 : (twinPrimeSegment 354680877 354811949).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 354680877 ≤ 354746413)
    (by decide : 354746413 ≤ 354811949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 354680877 354811949).card = 449 := join_1_0

end S169C02
end Sude.GeneratedTwinScan
