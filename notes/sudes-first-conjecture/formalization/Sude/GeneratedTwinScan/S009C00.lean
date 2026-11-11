import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 18874413 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 18874413 18907181).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 18874413 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 18874413 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 18874413 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 18907181 widths1 = 161 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 18907181 18939949).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 18907181 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 18907181 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 18907181 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 18939949 widths2 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 18939949 18972717).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 18939949 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 18939949 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 18939949 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 18972717 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 18972717 19005485).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 18972717 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 18972717 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 18972717 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 18874413 18939949).card = 312 := by
  simpa using combineTwinPrimeSegments (by decide : 18874413 ≤ 18907181)
    (by decide : 18907181 ≤ 18939949) block0 block1

theorem join_0_1 : (twinPrimeSegment 18939949 19005485).card = 300 := by
  simpa using combineTwinPrimeSegments (by decide : 18939949 ≤ 18972717)
    (by decide : 18972717 ≤ 19005485) block2 block3

theorem join_1_0 : (twinPrimeSegment 18874413 19005485).card = 612 := by
  simpa using combineTwinPrimeSegments (by decide : 18874413 ≤ 18939949)
    (by decide : 18939949 ≤ 19005485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 18874413 19005485).card = 612 := join_1_0

end S009C00
end Sude.GeneratedTwinScan
