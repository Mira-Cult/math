import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125960237 125993005 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 125960237 125993005).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125960237 125993005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125993005 126025773 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 125993005 126025773).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125993005 126025773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126025773 126058541 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126025773 126058541).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126025773 126058541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126058541 126091309 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126058541 126091309).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126058541 126091309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 125960237 126025773).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 125960237 ≤ 125993005)
    (by decide : 125993005 ≤ 126025773) block0 block1

theorem join_0_1 : (twinPrimeSegment 126025773 126091309).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 126025773 ≤ 126058541)
    (by decide : 126058541 ≤ 126091309) block2 block3

theorem join_1_0 : (twinPrimeSegment 125960237 126091309).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 125960237 ≤ 126025773)
    (by decide : 126025773 ≤ 126091309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 125960237 126091309).card = 481 := join_1_0

end S060C01
end Sude.GeneratedTwinScan
