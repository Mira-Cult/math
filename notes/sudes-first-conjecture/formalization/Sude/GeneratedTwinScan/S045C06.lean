import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95158317 95191085 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95158317 95191085).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95158317 95191085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95191085 95223853 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95191085 95223853).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95191085 95223853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95223853 95256621 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95223853 95256621).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95223853 95256621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95256621 95289389 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95256621 95289389).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95256621 95289389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95158317 95223853).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 95158317 ≤ 95191085)
    (by decide : 95191085 ≤ 95223853) block0 block1

theorem join_0_1 : (twinPrimeSegment 95223853 95289389).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 95223853 ≤ 95256621)
    (by decide : 95256621 ≤ 95289389) block2 block3

theorem join_1_0 : (twinPrimeSegment 95158317 95289389).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 95158317 ≤ 95223853)
    (by decide : 95223853 ≤ 95289389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95158317 95289389).card = 517 := join_1_0

end S045C06
end Sude.GeneratedTwinScan
