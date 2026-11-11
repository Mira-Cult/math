import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 26738733 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 26738733 26771501).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26738733 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26738733 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26738733 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 26771501 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 26771501 26804269).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26771501 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26771501 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26771501 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 26804269 widths2 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 26804269 26837037).card = 127 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26804269 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26804269 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26804269 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 26837037 widths3 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 26837037 26869805).card = 136 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26837037 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26837037 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26837037 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 26738733 26804269).card = 299 := by
  simpa using combineTwinPrimeSegments (by decide : 26738733 ≤ 26771501)
    (by decide : 26771501 ≤ 26804269) block0 block1

theorem join_0_1 : (twinPrimeSegment 26804269 26869805).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 26804269 ≤ 26837037)
    (by decide : 26837037 ≤ 26869805) block2 block3

theorem join_1_0 : (twinPrimeSegment 26738733 26869805).card = 562 := by
  simpa using combineTwinPrimeSegments (by decide : 26738733 ≤ 26804269)
    (by decide : 26804269 ≤ 26869805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 26738733 26869805).card = 562 := join_1_0

end S012C12
end Sude.GeneratedTwinScan
