import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 15597613 widths0 = 158 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 15597613 15630381).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15597613 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15597613 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15597613 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 15630381 widths1 = 149 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 15630381 15663149).card = 149 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15630381 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15630381 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15630381 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 15663149 widths2 = 162 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 15663149 15695917).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15663149 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15663149 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15663149 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 15695917 widths3 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 15695917 15728685).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15695917 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15695917 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15695917 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 15597613 15663149).card = 307 := by
  simpa using combineTwinPrimeSegments (by decide : 15597613 ≤ 15630381)
    (by decide : 15630381 ≤ 15663149) block0 block1

theorem join_0_1 : (twinPrimeSegment 15663149 15728685).card = 319 := by
  simpa using combineTwinPrimeSegments (by decide : 15663149 ≤ 15695917)
    (by decide : 15695917 ≤ 15728685) block2 block3

theorem join_1_0 : (twinPrimeSegment 15597613 15728685).card = 626 := by
  simpa using combineTwinPrimeSegments (by decide : 15597613 ≤ 15663149)
    (by decide : 15663149 ≤ 15728685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 15597613 15728685).card = 626 := join_1_0

end S007C07
end Sude.GeneratedTwinScan
