import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 10747949 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 10747949 10780717).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10747949 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10747949 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10747949 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 10780717 widths1 = 165 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 10780717 10813485).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10780717 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10780717 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10780717 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 10813485 widths2 = 164 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 10813485 10846253).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10813485 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10813485 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10813485 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 10846253 widths3 = 167 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 10846253 10879021).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10846253 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10846253 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10846253 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 10747949 10813485).card = 316 := by
  simpa using combineTwinPrimeSegments (by decide : 10747949 ≤ 10780717)
    (by decide : 10780717 ≤ 10813485) block0 block1

theorem join_0_1 : (twinPrimeSegment 10813485 10879021).card = 331 := by
  simpa using combineTwinPrimeSegments (by decide : 10813485 ≤ 10846253)
    (by decide : 10846253 ≤ 10879021) block2 block3

theorem join_1_0 : (twinPrimeSegment 10747949 10879021).card = 647 := by
  simpa using combineTwinPrimeSegments (by decide : 10747949 ≤ 10813485)
    (by decide : 10813485 ≤ 10879021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 10747949 10879021).card = 647 := join_1_0

end S005C02
end Sude.GeneratedTwinScan
