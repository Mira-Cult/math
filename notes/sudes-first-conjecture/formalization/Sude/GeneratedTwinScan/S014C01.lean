import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 29491245 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 29491245 29524013).card = 135 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29491245 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29491245 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29491245 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 29524013 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 29524013 29556781).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29524013 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29524013 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29524013 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 29556781 widths2 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 29556781 29589549).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29556781 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29556781 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29556781 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 29589549 widths3 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 29589549 29622317).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29589549 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29589549 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29589549 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 29491245 29556781).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 29491245 ≤ 29524013)
    (by decide : 29524013 ≤ 29556781) block0 block1

theorem join_0_1 : (twinPrimeSegment 29556781 29622317).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 29556781 ≤ 29589549)
    (by decide : 29589549 ≤ 29622317) block2 block3

theorem join_1_0 : (twinPrimeSegment 29491245 29622317).card = 570 := by
  simpa using combineTwinPrimeSegments (by decide : 29491245 ≤ 29556781)
    (by decide : 29556781 ≤ 29622317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 29491245 29622317).card = 570 := join_1_0

end S014C01
end Sude.GeneratedTwinScan
