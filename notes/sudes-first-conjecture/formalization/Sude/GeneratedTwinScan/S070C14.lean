import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148635693 148668461 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148635693 148668461).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148635693 148668461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148668461 148701229 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148668461 148701229).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148668461 148701229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148701229 148733997 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148701229 148733997).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148701229 148733997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148733997 148766765 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148733997 148766765).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148733997 148766765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148635693 148701229).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 148635693 ≤ 148668461)
    (by decide : 148668461 ≤ 148701229) block0 block1

theorem join_0_1 : (twinPrimeSegment 148701229 148766765).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 148701229 ≤ 148733997)
    (by decide : 148733997 ≤ 148766765) block2 block3

theorem join_1_0 : (twinPrimeSegment 148635693 148766765).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 148635693 ≤ 148701229)
    (by decide : 148701229 ≤ 148766765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148635693 148766765).card = 478 := join_1_0

end S070C14
end Sude.GeneratedTwinScan
