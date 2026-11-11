import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C13

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 10223661 widths0 = 172 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 10223661 10256429).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10223661 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10223661 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10223661 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 10256429 widths1 = 182 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 10256429 10289197).card = 182 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10256429 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10256429 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10256429 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 10289197 widths2 = 160 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 10289197 10321965).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10289197 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10289197 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10289197 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 10321965 widths3 = 156 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 10321965 10354733).card = 156 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10321965 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10321965 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10321965 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 10223661 10289197).card = 354 := by
  simpa using combineTwinPrimeSegments (by decide : 10223661 ≤ 10256429)
    (by decide : 10256429 ≤ 10289197) block0 block1

theorem join_0_1 : (twinPrimeSegment 10289197 10354733).card = 316 := by
  simpa using combineTwinPrimeSegments (by decide : 10289197 ≤ 10321965)
    (by decide : 10321965 ≤ 10354733) block2 block3

theorem join_1_0 : (twinPrimeSegment 10223661 10354733).card = 670 := by
  simpa using combineTwinPrimeSegments (by decide : 10223661 ≤ 10289197)
    (by decide : 10289197 ≤ 10354733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 10223661 10354733).card = 670 := join_1_0

end S004C14
end Sude.GeneratedTwinScan
