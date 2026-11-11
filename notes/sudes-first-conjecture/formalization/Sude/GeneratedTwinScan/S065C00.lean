import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S065C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136314925 136347693 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 136314925 136347693).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136314925 136347693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136347693 136380461 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 136347693 136380461).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136347693 136380461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136380461 136413229 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 136380461 136413229).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136380461 136413229
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 136413229 136445997 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 136413229 136445997).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 136413229 136445997
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 136314925 136380461).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 136314925 ≤ 136347693)
    (by decide : 136347693 ≤ 136380461) block0 block1

theorem join_0_1 : (twinPrimeSegment 136380461 136445997).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 136380461 ≤ 136413229)
    (by decide : 136413229 ≤ 136445997) block2 block3

theorem join_1_0 : (twinPrimeSegment 136314925 136445997).card = 536 := by
  simpa using combineTwinPrimeSegments (by decide : 136314925 ≤ 136380461)
    (by decide : 136380461 ≤ 136445997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 136314925 136445997).card = 536 := join_1_0

end S065C00
end Sude.GeneratedTwinScan
