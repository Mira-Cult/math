import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120979501 121012269 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120979501 121012269).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120979501 121012269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121012269 121045037 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 121012269 121045037).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121012269 121045037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121045037 121077805 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 121045037 121077805).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121045037 121077805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 121077805 121110573 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 121077805 121110573).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 121077805 121110573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120979501 121045037).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 120979501 ≤ 121012269)
    (by decide : 121012269 ≤ 121045037) block0 block1

theorem join_0_1 : (twinPrimeSegment 121045037 121110573).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 121045037 ≤ 121077805)
    (by decide : 121077805 ≤ 121110573) block2 block3

theorem join_1_0 : (twinPrimeSegment 120979501 121110573).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 120979501 ≤ 121045037)
    (by decide : 121045037 ≤ 121110573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120979501 121110573).card = 492 := join_1_0

end S057C11
end Sude.GeneratedTwinScan
