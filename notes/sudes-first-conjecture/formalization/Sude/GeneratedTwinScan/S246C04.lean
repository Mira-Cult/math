import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22725)) 516423725 516456493 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516423725 516456493).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22725 516423725 516456493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22726)) 516456493 516489261 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516456493 516489261).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22726 516456493 516489261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22727)) 516489261 516522029 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 516489261 516522029).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22727 516489261 516522029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22727)) 516522029 516554797 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 516522029 516554797).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22727 516522029 516554797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516423725 516489261).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 516423725 ≤ 516456493)
    (by decide : 516456493 ≤ 516489261) block0 block1

theorem join_0_1 : (twinPrimeSegment 516489261 516554797).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 516489261 ≤ 516522029)
    (by decide : 516522029 ≤ 516554797) block2 block3

theorem join_1_0 : (twinPrimeSegment 516423725 516554797).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 516423725 ≤ 516489261)
    (by decide : 516489261 ≤ 516554797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516423725 516554797).card = 464 := join_1_0

end S246C04
end Sude.GeneratedTwinScan
