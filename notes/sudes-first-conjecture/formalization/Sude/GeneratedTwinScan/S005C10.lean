import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C09

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 11796525 widths0 = 166 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 11796525 11829293).card = 166 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11796525 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11796525 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11796525 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 11829293 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 11829293 11862061).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11829293 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11829293 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11829293 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 11862061 widths2 = 160 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 11862061 11894829).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11862061 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11862061 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11862061 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 11894829 widths3 = 162 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 11894829 11927597).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11894829 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11894829 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11894829 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 11796525 11862061).card = 313 := by
  simpa using combineTwinPrimeSegments (by decide : 11796525 ≤ 11829293)
    (by decide : 11829293 ≤ 11862061) block0 block1

theorem join_0_1 : (twinPrimeSegment 11862061 11927597).card = 322 := by
  simpa using combineTwinPrimeSegments (by decide : 11862061 ≤ 11894829)
    (by decide : 11894829 ≤ 11927597) block2 block3

theorem join_1_0 : (twinPrimeSegment 11796525 11927597).card = 635 := by
  simpa using combineTwinPrimeSegments (by decide : 11796525 ≤ 11862061)
    (by decide : 11862061 ≤ 11927597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 11796525 11927597).card = 635 := join_1_0

end S005C10
end Sude.GeneratedTwinScan
