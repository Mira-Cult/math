import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 6160429 widths0 = 168 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 6160429 6193197).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6160429 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6160429 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6160429 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 6193197 widths1 = 192 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 6193197 6225965).card = 192 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6193197 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6193197 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6193197 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 6225965 widths2 = 175 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 6225965 6258733).card = 175 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6225965 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6225965 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6225965 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 6258733 widths3 = 175 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 6258733 6291501).card = 175 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6258733 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6258733 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6258733 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 6160429 6225965).card = 360 := by
  simpa using combineTwinPrimeSegments (by decide : 6160429 ≤ 6193197)
    (by decide : 6193197 ≤ 6225965) block0 block1

theorem join_0_1 : (twinPrimeSegment 6225965 6291501).card = 350 := by
  simpa using combineTwinPrimeSegments (by decide : 6225965 ≤ 6258733)
    (by decide : 6258733 ≤ 6291501) block2 block3

theorem join_1_0 : (twinPrimeSegment 6160429 6291501).card = 710 := by
  simpa using combineTwinPrimeSegments (by decide : 6160429 ≤ 6225965)
    (by decide : 6225965 ≤ 6291501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 6160429 6291501).card = 710 := join_1_0

end S002C15
end Sude.GeneratedTwinScan
