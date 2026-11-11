import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 26607661 widths0 = 161 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 26607661 26640429).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26607661 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26607661 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26607661 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 26640429 widths1 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 26640429 26673197).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26640429 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26640429 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26640429 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 26673197 widths2 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 26673197 26705965).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26673197 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26673197 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26673197 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 26705965 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 26705965 26738733).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26705965 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26705965 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26705965 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 26607661 26673197).card = 311 := by
  simpa using combineTwinPrimeSegments (by decide : 26607661 ≤ 26640429)
    (by decide : 26640429 ≤ 26673197) block0 block1

theorem join_0_1 : (twinPrimeSegment 26673197 26738733).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 26673197 ≤ 26705965)
    (by decide : 26705965 ≤ 26738733) block2 block3

theorem join_1_0 : (twinPrimeSegment 26607661 26738733).card = 600 := by
  simpa using combineTwinPrimeSegments (by decide : 26607661 ≤ 26673197)
    (by decide : 26673197 ≤ 26738733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 26607661 26738733).card = 600 := join_1_0

end S012C11
end Sude.GeneratedTwinScan
