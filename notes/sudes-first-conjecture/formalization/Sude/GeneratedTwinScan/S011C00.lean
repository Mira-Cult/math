import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S011C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 23068717 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 23068717 23101485).card = 134 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 23068717 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 23068717 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 23068717 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 23101485 widths1 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 23101485 23134253).card = 145 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 23101485 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 23101485 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 23101485 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 23134253 widths2 = 157 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 23134253 23167021).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 23134253 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 23134253 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 23134253 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 23167021 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 23167021 23199789).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 23167021 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 23167021 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 23167021 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 23068717 23134253).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 23068717 ≤ 23101485)
    (by decide : 23101485 ≤ 23134253) block0 block1

theorem join_0_1 : (twinPrimeSegment 23134253 23199789).card = 303 := by
  simpa using combineTwinPrimeSegments (by decide : 23134253 ≤ 23167021)
    (by decide : 23167021 ≤ 23199789) block2 block3

theorem join_1_0 : (twinPrimeSegment 23068717 23199789).card = 582 := by
  simpa using combineTwinPrimeSegments (by decide : 23068717 ≤ 23134253)
    (by decide : 23134253 ≤ 23199789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 23068717 23199789).card = 582 := join_1_0

end S011C00
end Sude.GeneratedTwinScan
