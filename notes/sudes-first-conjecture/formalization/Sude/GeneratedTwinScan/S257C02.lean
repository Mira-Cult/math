import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 539230253 widths0 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 539230253 539263021).card = 116 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539230253 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539230253 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539230253 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 539263021 widths1 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 539263021 539295789).card = 109 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539263021 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539263021 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539263021 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 539295789 widths2 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 539295789 539328557).card = 106 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539295789 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539295789 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539295789 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 539328557 widths3 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 539328557 539361325).card = 103 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539328557 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539328557 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539328557 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 539230253 539295789).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 539230253 ≤ 539263021)
    (by decide : 539263021 ≤ 539295789) block0 block1

theorem join_0_1 : (twinPrimeSegment 539295789 539361325).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 539295789 ≤ 539328557)
    (by decide : 539328557 ≤ 539361325) block2 block3

theorem join_1_0 : (twinPrimeSegment 539230253 539361325).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 539230253 ≤ 539295789)
    (by decide : 539295789 ≤ 539361325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 539230253 539361325).card = 434 := join_1_0

end S257C02
end Sude.GeneratedTwinScan
