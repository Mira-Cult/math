import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121897005 121929773 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 121897005 121929773).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121897005 121929773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121929773 121962541 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121929773 121962541).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121929773 121962541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121962541 121995309 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121962541 121995309).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121962541 121995309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121995309 122028077 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121995309 122028077).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121995309 122028077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 121897005 121962541).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 121897005 ≤ 121929773)
    (by decide : 121929773 ≤ 121962541) block0 block1

theorem join_0_1 : (twinPrimeSegment 121962541 122028077).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 121962541 ≤ 121995309)
    (by decide : 121995309 ≤ 122028077) block2 block3

theorem join_1_0 : (twinPrimeSegment 121897005 122028077).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 121897005 ≤ 121962541)
    (by decide : 121962541 ≤ 122028077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 121897005 122028077).card = 473 := join_1_0

end S058C02
end Sude.GeneratedTwinScan
