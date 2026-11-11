import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S010C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 21495853 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 21495853 21528621).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21495853 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21495853 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21495853 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 21528621 widths1 = 169 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 21528621 21561389).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21528621 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21528621 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21528621 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 21561389 widths2 = 151 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 21561389 21594157).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21561389 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21561389 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21561389 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 21594157 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 21594157 21626925).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21594157 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21594157 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21594157 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 21495853 21561389).card = 315 := by
  simpa using combineTwinPrimeSegments (by decide : 21495853 ≤ 21528621)
    (by decide : 21528621 ≤ 21561389) block0 block1

theorem join_0_1 : (twinPrimeSegment 21561389 21626925).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 21561389 ≤ 21594157)
    (by decide : 21594157 ≤ 21626925) block2 block3

theorem join_1_0 : (twinPrimeSegment 21495853 21626925).card = 610 := by
  simpa using combineTwinPrimeSegments (by decide : 21495853 ≤ 21561389)
    (by decide : 21561389 ≤ 21626925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 21495853 21626925).card = 610 := join_1_0

end S010C04
end Sude.GeneratedTwinScan
