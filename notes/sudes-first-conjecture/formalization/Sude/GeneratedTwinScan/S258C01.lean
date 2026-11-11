import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 541196333 widths0 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 541196333 541229101).card = 94 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541196333 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541196333 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541196333 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 541229101 widths1 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 541229101 541261869).card = 104 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541229101 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541229101 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541229101 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 541261869 widths2 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 541261869 541294637).card = 99 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541261869 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541261869 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541261869 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 541294637 widths3 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 541294637 541327405).card = 96 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541294637 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541294637 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541294637 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 541196333 541261869).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 541196333 ≤ 541229101)
    (by decide : 541229101 ≤ 541261869) block0 block1

theorem join_0_1 : (twinPrimeSegment 541261869 541327405).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 541261869 ≤ 541294637)
    (by decide : 541294637 ≤ 541327405) block2 block3

theorem join_1_0 : (twinPrimeSegment 541196333 541327405).card = 393 := by
  simpa using combineTwinPrimeSegments (by decide : 541196333 ≤ 541261869)
    (by decide : 541261869 ≤ 541327405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 541196333 541327405).card = 393 := join_1_0

end S258C01
end Sude.GeneratedTwinScan
