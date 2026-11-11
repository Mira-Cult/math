import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19136557 widths0 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19136557 19169325).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19136557 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19136557 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19136557 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19169325 widths1 = 157 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19169325 19202093).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19169325 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19169325 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19169325 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19202093 widths2 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19202093 19234861).card = 131 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19202093 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19202093 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19202093 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 19234861 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 19234861 19267629).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19234861 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19234861 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19234861 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19136557 19202093).card = 301 := by
  simpa using combineTwinPrimeSegments (by decide : 19136557 ≤ 19169325)
    (by decide : 19169325 ≤ 19202093) block0 block1

theorem join_0_1 : (twinPrimeSegment 19202093 19267629).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 19202093 ≤ 19234861)
    (by decide : 19234861 ≤ 19267629) block2 block3

theorem join_1_0 : (twinPrimeSegment 19136557 19267629).card = 579 := by
  simpa using combineTwinPrimeSegments (by decide : 19136557 ≤ 19202093)
    (by decide : 19202093 ≤ 19267629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19136557 19267629).card = 579 := join_1_0

end S009C02
end Sude.GeneratedTwinScan
