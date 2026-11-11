import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S003C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S003C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 6553645 widths0 = 179 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 6553645 6586413).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6553645 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6553645 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6553645 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 6586413 widths1 = 174 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 6586413 6619181).card = 174 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6586413 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6586413 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6586413 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 6619181 widths2 = 160 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 6619181 6651949).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6619181 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6619181 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6619181 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 6651949 widths3 = 166 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 6651949 6684717).card = 166 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6651949 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6651949 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6651949 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 6553645 6619181).card = 353 := by
  simpa using combineTwinPrimeSegments (by decide : 6553645 ≤ 6586413)
    (by decide : 6586413 ≤ 6619181) block0 block1

theorem join_0_1 : (twinPrimeSegment 6619181 6684717).card = 326 := by
  simpa using combineTwinPrimeSegments (by decide : 6619181 ≤ 6651949)
    (by decide : 6651949 ≤ 6684717) block2 block3

theorem join_1_0 : (twinPrimeSegment 6553645 6684717).card = 679 := by
  simpa using combineTwinPrimeSegments (by decide : 6553645 ≤ 6619181)
    (by decide : 6619181 ≤ 6684717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 6553645 6684717).card = 679 := join_1_0

end S003C02
end Sude.GeneratedTwinScan
