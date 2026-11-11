import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19529773 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19529773 19562541).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19529773 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19529773 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19529773 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19562541 widths1 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19562541 19595309).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19562541 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19562541 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19562541 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19595309 widths2 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19595309 19628077).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19595309 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19595309 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19595309 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 19628077 widths3 = 161 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 19628077 19660845).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19628077 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19628077 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19628077 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19529773 19595309).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 19529773 ≤ 19562541)
    (by decide : 19562541 ≤ 19595309) block0 block1

theorem join_0_1 : (twinPrimeSegment 19595309 19660845).card = 313 := by
  simpa using combineTwinPrimeSegments (by decide : 19595309 ≤ 19628077)
    (by decide : 19628077 ≤ 19660845) block2 block3

theorem join_1_0 : (twinPrimeSegment 19529773 19660845).card = 607 := by
  simpa using combineTwinPrimeSegments (by decide : 19529773 ≤ 19595309)
    (by decide : 19595309 ≤ 19660845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19529773 19660845).card = 607 := join_1_0

end S009C05
end Sude.GeneratedTwinScan
