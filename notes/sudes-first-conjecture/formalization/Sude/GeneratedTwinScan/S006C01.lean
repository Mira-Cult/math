import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S006C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S006C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 12714029 widths0 = 172 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 12714029 12746797).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12714029 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12714029 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12714029 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 12746797 widths1 = 169 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 12746797 12779565).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12746797 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12746797 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12746797 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 12779565 widths2 = 164 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 12779565 12812333).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12779565 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12779565 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12779565 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 12812333 widths3 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 12812333 12845101).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12812333 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12812333 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12812333 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 12714029 12779565).card = 341 := by
  simpa using combineTwinPrimeSegments (by decide : 12714029 ≤ 12746797)
    (by decide : 12746797 ≤ 12779565) block0 block1

theorem join_0_1 : (twinPrimeSegment 12779565 12845101).card = 321 := by
  simpa using combineTwinPrimeSegments (by decide : 12779565 ≤ 12812333)
    (by decide : 12812333 ≤ 12845101) block2 block3

theorem join_1_0 : (twinPrimeSegment 12714029 12845101).card = 662 := by
  simpa using combineTwinPrimeSegments (by decide : 12714029 ≤ 12779565)
    (by decide : 12779565 ≤ 12845101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 12714029 12845101).card = 662 := join_1_0

end S006C01
end Sude.GeneratedTwinScan
