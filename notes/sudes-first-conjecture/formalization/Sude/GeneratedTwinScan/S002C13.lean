import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C12

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 5898285 widths0 = 193 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 5898285 5931053).card = 193 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5898285 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5898285 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5898285 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 5931053 widths1 = 164 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 5931053 5963821).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5931053 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5931053 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5931053 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 5963821 widths2 = 181 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 5963821 5996589).card = 181 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5963821 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5963821 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5963821 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 5996589 widths3 = 196 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 5996589 6029357).card = 196 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5996589 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5996589 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5996589 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 5898285 5963821).card = 357 := by
  simpa using combineTwinPrimeSegments (by decide : 5898285 ≤ 5931053)
    (by decide : 5931053 ≤ 5963821) block0 block1

theorem join_0_1 : (twinPrimeSegment 5963821 6029357).card = 377 := by
  simpa using combineTwinPrimeSegments (by decide : 5963821 ≤ 5996589)
    (by decide : 5996589 ≤ 6029357) block2 block3

theorem join_1_0 : (twinPrimeSegment 5898285 6029357).card = 734 := by
  simpa using combineTwinPrimeSegments (by decide : 5898285 ≤ 5963821)
    (by decide : 5963821 ≤ 6029357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 5898285 6029357).card = 734 := join_1_0

end S002C13
end Sude.GeneratedTwinScan
