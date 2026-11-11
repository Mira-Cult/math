import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 14811181 widths0 = 164 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 14811181 14843949).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14811181 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14811181 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14811181 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 14843949 widths1 = 172 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 14843949 14876717).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14843949 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14843949 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14843949 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 14876717 widths2 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 14876717 14909485).card = 139 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14876717 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14876717 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14876717 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 14909485 widths3 = 160 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 14909485 14942253).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 14909485 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 14909485 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 14909485 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 14811181 14876717).card = 336 := by
  simpa using combineTwinPrimeSegments (by decide : 14811181 ≤ 14843949)
    (by decide : 14843949 ≤ 14876717) block0 block1

theorem join_0_1 : (twinPrimeSegment 14876717 14942253).card = 299 := by
  simpa using combineTwinPrimeSegments (by decide : 14876717 ≤ 14909485)
    (by decide : 14909485 ≤ 14942253) block2 block3

theorem join_1_0 : (twinPrimeSegment 14811181 14942253).card = 635 := by
  simpa using combineTwinPrimeSegments (by decide : 14811181 ≤ 14876717)
    (by decide : 14876717 ≤ 14942253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 14811181 14942253).card = 635 := join_1_0

end S007C01
end Sude.GeneratedTwinScan
