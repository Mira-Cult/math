import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 10485805 widths0 = 175 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 10485805 10518573).card = 175 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10485805 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10485805 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10485805 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 10518573 widths1 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 10518573 10551341).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10518573 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10518573 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10518573 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 10551341 widths2 = 157 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 10551341 10584109).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10551341 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10551341 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10551341 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 10584109 widths3 = 168 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 10584109 10616877).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10584109 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10584109 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10584109 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 10485805 10551341).card = 327 := by
  simpa using combineTwinPrimeSegments (by decide : 10485805 ≤ 10518573)
    (by decide : 10518573 ≤ 10551341) block0 block1

theorem join_0_1 : (twinPrimeSegment 10551341 10616877).card = 325 := by
  simpa using combineTwinPrimeSegments (by decide : 10551341 ≤ 10584109)
    (by decide : 10584109 ≤ 10616877) block2 block3

theorem join_1_0 : (twinPrimeSegment 10485805 10616877).card = 652 := by
  simpa using combineTwinPrimeSegments (by decide : 10485805 ≤ 10551341)
    (by decide : 10551341 ≤ 10616877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 10485805 10616877).card = 652 := join_1_0

end S005C00
end Sude.GeneratedTwinScan
