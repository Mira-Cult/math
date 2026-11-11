import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116916269 116949037 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 116916269 116949037).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116916269 116949037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116949037 116981805 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 116949037 116981805).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116949037 116981805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 116981805 117014573 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 116981805 117014573).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 116981805 117014573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 117014573 117047341 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 117014573 117047341).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 117014573 117047341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 116916269 116981805).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 116916269 ≤ 116949037)
    (by decide : 116949037 ≤ 116981805) block0 block1

theorem join_0_1 : (twinPrimeSegment 116981805 117047341).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 116981805 ≤ 117014573)
    (by decide : 117014573 ≤ 117047341) block2 block3

theorem join_1_0 : (twinPrimeSegment 116916269 117047341).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 116916269 ≤ 116981805)
    (by decide : 116981805 ≤ 117047341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 116916269 117047341).card = 491 := join_1_0

end S055C12
end Sude.GeneratedTwinScan
