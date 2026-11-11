import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 541720621 widths0 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 541720621 541753389).card = 105 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541720621 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541720621 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541720621 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 541753389 widths1 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 541753389 541786157).card = 101 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541753389 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541753389 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541753389 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 541786157 widths2 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 541786157 541818925).card = 97 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541786157 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541786157 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541786157 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 541818925 widths3 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 541818925 541851693).card = 111 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541818925 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541818925 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541818925 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 541720621 541786157).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 541720621 ≤ 541753389)
    (by decide : 541753389 ≤ 541786157) block0 block1

theorem join_0_1 : (twinPrimeSegment 541786157 541851693).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 541786157 ≤ 541818925)
    (by decide : 541818925 ≤ 541851693) block2 block3

theorem join_1_0 : (twinPrimeSegment 541720621 541851693).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 541720621 ≤ 541786157)
    (by decide : 541786157 ≤ 541851693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 541720621 541851693).card = 414 := join_1_0

end S258C05
end Sude.GeneratedTwinScan
