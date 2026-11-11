import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S010C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20971565 widths0 = 155 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20971565 21004333).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20971565 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20971565 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20971565 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 21004333 widths1 = 168 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 21004333 21037101).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21004333 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21004333 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21004333 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 21037101 widths2 = 169 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 21037101 21069869).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21037101 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21037101 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21037101 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 21069869 widths3 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 21069869 21102637).card = 132 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21069869 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21069869 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21069869 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20971565 21037101).card = 323 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 21004333)
    (by decide : 21004333 ≤ 21037101) block0 block1

theorem join_0_1 : (twinPrimeSegment 21037101 21102637).card = 301 := by
  simpa using combineTwinPrimeSegments (by decide : 21037101 ≤ 21069869)
    (by decide : 21069869 ≤ 21102637) block2 block3

theorem join_1_0 : (twinPrimeSegment 20971565 21102637).card = 624 := by
  simpa using combineTwinPrimeSegments (by decide : 20971565 ≤ 21037101)
    (by decide : 21037101 ≤ 21102637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20971565 21102637).card = 624 := join_1_0

end S010C00
end Sude.GeneratedTwinScan
