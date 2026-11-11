import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C12

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 16384045 widths0 = 167 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 16384045 16416813).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16384045 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16384045 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16384045 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 16416813 widths1 = 178 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 16416813 16449581).card = 178 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16416813 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16416813 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16416813 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 16449581 widths2 = 169 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 16449581 16482349).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16449581 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16449581 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16449581 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 16482349 widths3 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 16482349 16515117).card = 136 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16482349 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16482349 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16482349 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 16384045 16449581).card = 345 := by
  simpa using combineTwinPrimeSegments (by decide : 16384045 ≤ 16416813)
    (by decide : 16416813 ≤ 16449581) block0 block1

theorem join_0_1 : (twinPrimeSegment 16449581 16515117).card = 305 := by
  simpa using combineTwinPrimeSegments (by decide : 16449581 ≤ 16482349)
    (by decide : 16482349 ≤ 16515117) block2 block3

theorem join_1_0 : (twinPrimeSegment 16384045 16515117).card = 650 := by
  simpa using combineTwinPrimeSegments (by decide : 16384045 ≤ 16449581)
    (by decide : 16449581 ≤ 16515117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 16384045 16515117).card = 650 := join_1_0

end S007C13
end Sude.GeneratedTwinScan
