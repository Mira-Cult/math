import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S178C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19345)) 374210605 374243373 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 374210605 374243373).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19345 374210605 374243373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19346)) 374243373 374276141 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 374243373 374276141).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19346 374243373 374276141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19347)) 374276141 374308909 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 374276141 374308909).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19347 374276141 374308909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19347)) 374308909 374341677 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 374308909 374341677).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19347 374308909 374341677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 374210605 374276141).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 374210605 ≤ 374243373)
    (by decide : 374243373 ≤ 374276141) block0 block1

theorem join_0_1 : (twinPrimeSegment 374276141 374341677).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 374276141 ≤ 374308909)
    (by decide : 374308909 ≤ 374341677) block2 block3

theorem join_1_0 : (twinPrimeSegment 374210605 374341677).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 374210605 ≤ 374276141)
    (by decide : 374276141 ≤ 374341677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 374210605 374341677).card = 455 := join_1_0

end S178C07
end Sude.GeneratedTwinScan
