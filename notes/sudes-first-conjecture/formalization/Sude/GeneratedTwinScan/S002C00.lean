import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 4194349 widths0 = 191 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 4194349 4227117).card = 191 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4194349 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4194349 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4194349 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 4227117 widths1 = 189 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 4227117 4259885).card = 189 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4227117 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4227117 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4227117 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 4259885 widths2 = 173 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 4259885 4292653).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4259885 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4259885 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4259885 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 4292653 widths3 = 171 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 4292653 4325421).card = 171 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4292653 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4292653 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4292653 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 4194349 4259885).card = 380 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 4227117)
    (by decide : 4227117 ≤ 4259885) block0 block1

theorem join_0_1 : (twinPrimeSegment 4259885 4325421).card = 344 := by
  simpa using combineTwinPrimeSegments (by decide : 4259885 ≤ 4292653)
    (by decide : 4292653 ≤ 4325421) block2 block3

theorem join_1_0 : (twinPrimeSegment 4194349 4325421).card = 724 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 4259885)
    (by decide : 4259885 ≤ 4325421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 4194349 4325421).card = 724 := join_1_0

end S002C00
end Sude.GeneratedTwinScan
