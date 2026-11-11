import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C02

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19267629 widths0 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19267629 19300397).card = 137 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19267629 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19267629 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19267629 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19300397 widths1 = 161 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19300397 19333165).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19300397 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19300397 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19300397 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19333165 widths2 = 158 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19333165 19365933).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19333165 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19333165 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19333165 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 19365933 widths3 = 170 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 19365933 19398701).card = 170 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19365933 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19365933 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19365933 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19267629 19333165).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 19267629 ≤ 19300397)
    (by decide : 19300397 ≤ 19333165) block0 block1

theorem join_0_1 : (twinPrimeSegment 19333165 19398701).card = 328 := by
  simpa using combineTwinPrimeSegments (by decide : 19333165 ≤ 19365933)
    (by decide : 19365933 ≤ 19398701) block2 block3

theorem join_1_0 : (twinPrimeSegment 19267629 19398701).card = 626 := by
  simpa using combineTwinPrimeSegments (by decide : 19267629 ≤ 19333165)
    (by decide : 19333165 ≤ 19398701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19267629 19398701).card = 626 := join_1_0

end S009C03
end Sude.GeneratedTwinScan
