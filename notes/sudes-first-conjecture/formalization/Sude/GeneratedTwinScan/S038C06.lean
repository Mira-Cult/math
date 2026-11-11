import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S038C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80478253 80511021 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 80478253 80511021).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80478253 80511021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80511021 80543789 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 80511021 80543789).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80511021 80543789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80543789 80576557 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 80543789 80576557).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80543789 80576557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 80576557 80609325 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 80576557 80609325).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 80576557 80609325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 80478253 80543789).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 80478253 ≤ 80511021)
    (by decide : 80511021 ≤ 80543789) block0 block1

theorem join_0_1 : (twinPrimeSegment 80543789 80609325).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 80543789 ≤ 80576557)
    (by decide : 80576557 ≤ 80609325) block2 block3

theorem join_1_0 : (twinPrimeSegment 80478253 80609325).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 80478253 ≤ 80543789)
    (by decide : 80543789 ≤ 80609325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 80478253 80609325).card = 504 := join_1_0

end S038C06
end Sude.GeneratedTwinScan
