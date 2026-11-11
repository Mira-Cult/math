import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S006C02

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S006C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 12976173 widths0 = 162 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 12976173 13008941).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12976173 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12976173 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12976173 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 13008941 widths1 = 164 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 13008941 13041709).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13008941 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13008941 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13008941 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 13041709 widths2 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 13041709 13074477).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13041709 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13041709 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13041709 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 13074477 widths3 = 154 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 13074477 13107245).card = 154 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13074477 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13074477 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13074477 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 12976173 13041709).card = 326 := by
  simpa using combineTwinPrimeSegments (by decide : 12976173 ≤ 13008941)
    (by decide : 13008941 ≤ 13041709) block0 block1

theorem join_0_1 : (twinPrimeSegment 13041709 13107245).card = 301 := by
  simpa using combineTwinPrimeSegments (by decide : 13041709 ≤ 13074477)
    (by decide : 13074477 ≤ 13107245) block2 block3

theorem join_1_0 : (twinPrimeSegment 12976173 13107245).card = 627 := by
  simpa using combineTwinPrimeSegments (by decide : 12976173 ≤ 13041709)
    (by decide : 13041709 ≤ 13107245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 12976173 13107245).card = 627 := join_1_0

end S006C03
end Sude.GeneratedTwinScan
