import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105513005 105545773 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105513005 105545773).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105513005 105545773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105545773 105578541 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105545773 105578541).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105545773 105578541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105578541 105611309 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105578541 105611309).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105578541 105611309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105611309 105644077 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105611309 105644077).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105611309 105644077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105513005 105578541).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 105513005 ≤ 105545773)
    (by decide : 105545773 ≤ 105578541) block0 block1

theorem join_0_1 : (twinPrimeSegment 105578541 105644077).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 105578541 ≤ 105611309)
    (by decide : 105611309 ≤ 105644077) block2 block3

theorem join_1_0 : (twinPrimeSegment 105513005 105644077).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 105513005 ≤ 105578541)
    (by decide : 105578541 ≤ 105644077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105513005 105644077).card = 502 := join_1_0

end S050C05
end Sude.GeneratedTwinScan
