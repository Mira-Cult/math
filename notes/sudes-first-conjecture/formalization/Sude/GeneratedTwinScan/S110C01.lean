import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15193)) 230817837 230850605 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230817837 230850605).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15193 230817837 230850605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15194)) 230850605 230883373 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230850605 230883373).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15194 230850605 230883373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15195)) 230883373 230916141 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 230883373 230916141).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15195 230883373 230916141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15197)) 230916141 230948909 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 230916141 230948909).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15197 230916141 230948909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230817837 230883373).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 230817837 ≤ 230850605)
    (by decide : 230850605 ≤ 230883373) block0 block1

theorem join_0_1 : (twinPrimeSegment 230883373 230948909).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 230883373 ≤ 230916141)
    (by decide : 230916141 ≤ 230948909) block2 block3

theorem join_1_0 : (twinPrimeSegment 230817837 230948909).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 230817837 ≤ 230883373)
    (by decide : 230883373 ≤ 230948909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230817837 230948909).card = 449 := join_1_0

end S110C01
end Sude.GeneratedTwinScan
