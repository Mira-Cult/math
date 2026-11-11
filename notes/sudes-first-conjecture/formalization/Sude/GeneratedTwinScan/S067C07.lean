import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141426733 141459501 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 141426733 141459501).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141426733 141459501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141459501 141492269 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 141459501 141492269).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141459501 141492269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141492269 141525037 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 141492269 141525037).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141492269 141525037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 141525037 141557805 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 141525037 141557805).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 141525037 141557805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 141426733 141492269).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 141426733 ≤ 141459501)
    (by decide : 141459501 ≤ 141492269) block0 block1

theorem join_0_1 : (twinPrimeSegment 141492269 141557805).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 141492269 ≤ 141525037)
    (by decide : 141525037 ≤ 141557805) block2 block3

theorem join_1_0 : (twinPrimeSegment 141426733 141557805).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 141426733 ≤ 141492269)
    (by decide : 141492269 ≤ 141557805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 141426733 141557805).card = 512 := join_1_0

end S067C07
end Sude.GeneratedTwinScan
