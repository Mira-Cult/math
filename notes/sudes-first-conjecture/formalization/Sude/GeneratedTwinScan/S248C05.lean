import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S248C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22820)) 520749101 520781869 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 520749101 520781869).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22820 520749101 520781869
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22821)) 520781869 520814637 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 520781869 520814637).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22821 520781869 520814637
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22822)) 520814637 520847405 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 520814637 520847405).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22822 520814637 520847405
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22822)) 520847405 520880173 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 520847405 520880173).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22822 520847405 520880173
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 520749101 520814637).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 520749101 ≤ 520781869)
    (by decide : 520781869 ≤ 520814637) block0 block1

theorem join_0_1 : (twinPrimeSegment 520814637 520880173).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 520814637 ≤ 520847405)
    (by decide : 520847405 ≤ 520880173) block2 block3

theorem join_1_0 : (twinPrimeSegment 520749101 520880173).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 520749101 ≤ 520814637)
    (by decide : 520814637 ≤ 520880173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 520749101 520880173).card = 434 := join_1_0

end S248C05
end Sude.GeneratedTwinScan
