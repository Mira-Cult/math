import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 5111853 widths0 = 180 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 5111853 5144621).card = 180 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5111853 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5111853 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5111853 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 5144621 widths1 = 188 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 5144621 5177389).card = 188 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5144621 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5144621 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5144621 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 5177389 widths2 = 183 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 5177389 5210157).card = 183 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5177389 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5177389 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5177389 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 5210157 widths3 = 163 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 5210157 5242925).card = 163 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5210157 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5210157 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5210157 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 5111853 5177389).card = 368 := by
  simpa using combineTwinPrimeSegments (by decide : 5111853 ≤ 5144621)
    (by decide : 5144621 ≤ 5177389) block0 block1

theorem join_0_1 : (twinPrimeSegment 5177389 5242925).card = 346 := by
  simpa using combineTwinPrimeSegments (by decide : 5177389 ≤ 5210157)
    (by decide : 5210157 ≤ 5242925) block2 block3

theorem join_1_0 : (twinPrimeSegment 5111853 5242925).card = 714 := by
  simpa using combineTwinPrimeSegments (by decide : 5111853 ≤ 5177389)
    (by decide : 5177389 ≤ 5242925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 5111853 5242925).card = 714 := join_1_0

end S002C07
end Sude.GeneratedTwinScan
