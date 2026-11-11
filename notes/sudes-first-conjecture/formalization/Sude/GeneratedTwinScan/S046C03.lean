import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96862253 96895021 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96862253 96895021).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96862253 96895021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96895021 96927789 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 96895021 96927789).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96895021 96927789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96927789 96960557 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96927789 96960557).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96927789 96960557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96960557 96993325 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96960557 96993325).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96960557 96993325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96862253 96927789).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 96862253 ≤ 96895021)
    (by decide : 96895021 ≤ 96927789) block0 block1

theorem join_0_1 : (twinPrimeSegment 96927789 96993325).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 96927789 ≤ 96960557)
    (by decide : 96960557 ≤ 96993325) block2 block3

theorem join_1_0 : (twinPrimeSegment 96862253 96993325).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 96862253 ≤ 96927789)
    (by decide : 96927789 ≤ 96993325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96862253 96993325).card = 504 := join_1_0

end S046C03
end Sude.GeneratedTwinScan
