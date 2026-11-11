import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19005485 widths0 = 159 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19005485 19038253).card = 159 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19005485 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19005485 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19005485 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19038253 widths1 = 154 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19038253 19071021).card = 154 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19038253 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19038253 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19038253 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19071021 widths2 = 160 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19071021 19103789).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19071021 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19071021 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19071021 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 19103789 widths3 = 173 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 19103789 19136557).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19103789 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19103789 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19103789 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19005485 19071021).card = 313 := by
  simpa using combineTwinPrimeSegments (by decide : 19005485 ≤ 19038253)
    (by decide : 19038253 ≤ 19071021) block0 block1

theorem join_0_1 : (twinPrimeSegment 19071021 19136557).card = 333 := by
  simpa using combineTwinPrimeSegments (by decide : 19071021 ≤ 19103789)
    (by decide : 19103789 ≤ 19136557) block2 block3

theorem join_1_0 : (twinPrimeSegment 19005485 19136557).card = 646 := by
  simpa using combineTwinPrimeSegments (by decide : 19005485 ≤ 19071021)
    (by decide : 19071021 ≤ 19136557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19005485 19136557).card = 646 := join_1_0

end S009C01
end Sude.GeneratedTwinScan
