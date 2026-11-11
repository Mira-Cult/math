import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C11

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 16252973 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 16252973 16285741).card = 145 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16252973 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16252973 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16252973 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 16285741 widths1 = 162 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 16285741 16318509).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16285741 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16285741 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16285741 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 16318509 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 16318509 16351277).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16318509 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16318509 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16318509 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 16351277 widths3 = 161 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 16351277 16384045).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16351277 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16351277 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16351277 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 16252973 16318509).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 16252973 ≤ 16285741)
    (by decide : 16285741 ≤ 16318509) block0 block1

theorem join_0_1 : (twinPrimeSegment 16318509 16384045).card = 302 := by
  simpa using combineTwinPrimeSegments (by decide : 16318509 ≤ 16351277)
    (by decide : 16351277 ≤ 16384045) block2 block3

theorem join_1_0 : (twinPrimeSegment 16252973 16384045).card = 609 := by
  simpa using combineTwinPrimeSegments (by decide : 16252973 ≤ 16318509)
    (by decide : 16318509 ≤ 16384045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 16252973 16384045).card = 609 := join_1_0

end S007C12
end Sude.GeneratedTwinScan
