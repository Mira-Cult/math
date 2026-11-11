import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117833773 117866541 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 117833773 117866541).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117833773 117866541
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117866541 117899309 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 117866541 117899309).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117866541 117899309
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117899309 117932077 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 117899309 117932077).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117899309 117932077
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117932077 117964845 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117932077 117964845).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117932077 117964845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 117833773 117899309).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 117833773 ≤ 117866541)
    (by decide : 117866541 ≤ 117899309) block0 block1

theorem join_0_1 : (twinPrimeSegment 117899309 117964845).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 117899309 ≤ 117932077)
    (by decide : 117932077 ≤ 117964845) block2 block3

theorem join_1_0 : (twinPrimeSegment 117833773 117964845).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 117833773 ≤ 117899309)
    (by decide : 117899309 ≤ 117964845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 117833773 117964845).card = 493 := join_1_0

end S056C03
end Sude.GeneratedTwinScan
