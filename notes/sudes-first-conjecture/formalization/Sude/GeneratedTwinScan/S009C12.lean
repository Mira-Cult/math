import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C11

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20447277 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20447277 20480045).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20447277 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20447277 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20447277 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 20480045 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 20480045 20512813).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20480045 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20480045 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20480045 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 20512813 widths2 = 156 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 20512813 20545581).card = 156 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20512813 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20512813 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20512813 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20545581 widths3 = 154 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20545581 20578349).card = 154 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20545581 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20545581 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20545581 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20447277 20512813).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 20447277 ≤ 20480045)
    (by decide : 20480045 ≤ 20512813) block0 block1

theorem join_0_1 : (twinPrimeSegment 20512813 20578349).card = 310 := by
  simpa using combineTwinPrimeSegments (by decide : 20512813 ≤ 20545581)
    (by decide : 20545581 ≤ 20578349) block2 block3

theorem join_1_0 : (twinPrimeSegment 20447277 20578349).card = 604 := by
  simpa using combineTwinPrimeSegments (by decide : 20447277 ≤ 20512813)
    (by decide : 20512813 ≤ 20578349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20447277 20578349).card = 604 := join_1_0

end S009C12
end Sude.GeneratedTwinScan
