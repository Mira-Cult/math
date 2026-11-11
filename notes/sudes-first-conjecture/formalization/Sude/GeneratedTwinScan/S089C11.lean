import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13715)) 188088365 188121133 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 188088365 188121133).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13715 188088365 188121133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13716)) 188121133 188153901 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 188121133 188153901).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13716 188121133 188153901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13718)) 188153901 188186669 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188153901 188186669).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13718 188153901 188186669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13719)) 188186669 188219437 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188186669 188219437).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13719 188186669 188219437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 188088365 188153901).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 188088365 ≤ 188121133)
    (by decide : 188121133 ≤ 188153901) block0 block1

theorem join_0_1 : (twinPrimeSegment 188153901 188219437).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 188153901 ≤ 188186669)
    (by decide : 188186669 ≤ 188219437) block2 block3

theorem join_1_0 : (twinPrimeSegment 188088365 188219437).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 188088365 ≤ 188153901)
    (by decide : 188153901 ≤ 188219437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 188088365 188219437).card = 464 := join_1_0

end S089C11
end Sude.GeneratedTwinScan
