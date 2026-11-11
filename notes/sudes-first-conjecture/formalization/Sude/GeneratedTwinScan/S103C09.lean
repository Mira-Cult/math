import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S103C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14738)) 217186349 217219117 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 217186349 217219117).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14738 217186349 217219117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14739)) 217219117 217251885 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 217219117 217251885).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14739 217219117 217251885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14740)) 217251885 217284653 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 217251885 217284653).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14740 217251885 217284653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14741)) 217284653 217317421 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 217284653 217317421).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14741 217284653 217317421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 217186349 217251885).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 217186349 ≤ 217219117)
    (by decide : 217219117 ≤ 217251885) block0 block1

theorem join_0_1 : (twinPrimeSegment 217251885 217317421).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 217251885 ≤ 217284653)
    (by decide : 217284653 ≤ 217317421) block2 block3

theorem join_1_0 : (twinPrimeSegment 217186349 217317421).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 217186349 ≤ 217251885)
    (by decide : 217251885 ≤ 217317421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 217186349 217317421).card = 449 := join_1_0

end S103C09
end Sude.GeneratedTwinScan
