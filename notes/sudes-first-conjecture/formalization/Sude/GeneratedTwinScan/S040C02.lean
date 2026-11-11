import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84148269 84181037 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84148269 84181037).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84148269 84181037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84181037 84213805 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84181037 84213805).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84181037 84213805
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84213805 84246573 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84213805 84246573).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84213805 84246573
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84246573 84279341 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84246573 84279341).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84246573 84279341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84148269 84213805).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 84148269 ≤ 84181037)
    (by decide : 84181037 ≤ 84213805) block0 block1

theorem join_0_1 : (twinPrimeSegment 84213805 84279341).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 84213805 ≤ 84246573)
    (by decide : 84246573 ≤ 84279341) block2 block3

theorem join_1_0 : (twinPrimeSegment 84148269 84279341).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 84148269 ≤ 84213805)
    (by decide : 84213805 ≤ 84279341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84148269 84279341).card = 530 := join_1_0

end S040C02
end Sude.GeneratedTwinScan
