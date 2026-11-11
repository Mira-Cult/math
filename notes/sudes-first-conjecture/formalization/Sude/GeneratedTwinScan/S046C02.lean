import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96731181 96763949 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 96731181 96763949).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96731181 96763949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96763949 96796717 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 96763949 96796717).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96763949 96796717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96796717 96829485 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 96796717 96829485).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96796717 96829485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 96829485 96862253 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 96829485 96862253).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 96829485 96862253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 96731181 96796717).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 96731181 ≤ 96763949)
    (by decide : 96763949 ≤ 96796717) block0 block1

theorem join_0_1 : (twinPrimeSegment 96796717 96862253).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 96796717 ≤ 96829485)
    (by decide : 96829485 ≤ 96862253) block2 block3

theorem join_1_0 : (twinPrimeSegment 96731181 96862253).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 96731181 ≤ 96796717)
    (by decide : 96796717 ≤ 96862253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 96731181 96862253).card = 512 := join_1_0

end S046C02
end Sude.GeneratedTwinScan
