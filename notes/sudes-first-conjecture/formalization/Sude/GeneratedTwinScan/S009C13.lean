import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C12

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20578349 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20578349 20611117).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20578349 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20578349 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20578349 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 20611117 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 20611117 20643885).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20611117 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20611117 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20611117 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 20643885 widths2 = 156 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 20643885 20676653).card = 156 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20643885 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20643885 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20643885 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20676653 widths3 = 156 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20676653 20709421).card = 156 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20676653 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20676653 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20676653 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20578349 20643885).card = 291 := by
  simpa using combineTwinPrimeSegments (by decide : 20578349 ≤ 20611117)
    (by decide : 20611117 ≤ 20643885) block0 block1

theorem join_0_1 : (twinPrimeSegment 20643885 20709421).card = 312 := by
  simpa using combineTwinPrimeSegments (by decide : 20643885 ≤ 20676653)
    (by decide : 20676653 ≤ 20709421) block2 block3

theorem join_1_0 : (twinPrimeSegment 20578349 20709421).card = 603 := by
  simpa using combineTwinPrimeSegments (by decide : 20578349 ≤ 20643885)
    (by decide : 20643885 ≤ 20709421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20578349 20709421).card = 603 := join_1_0

end S009C13
end Sude.GeneratedTwinScan
