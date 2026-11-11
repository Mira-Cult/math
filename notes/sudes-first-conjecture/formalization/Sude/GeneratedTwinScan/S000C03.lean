import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C02

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 393261 widths0 = 261 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393261 426029).card = 261 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 393261 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 393261 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 393261 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 426029 widths1 = 251 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 426029 458797).card = 251 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 426029 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 426029 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 426029 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 458797 widths2 = 242 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 458797 491565).card = 242 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 458797 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 458797 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 458797 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 491565 widths3 = 245 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 491565 524333).card = 245 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 491565 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 491565 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 491565 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 393261 458797).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 393261 ≤ 426029)
    (by decide : 426029 ≤ 458797) block0 block1

theorem join_0_1 : (twinPrimeSegment 458797 524333).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 458797 ≤ 491565)
    (by decide : 491565 ≤ 524333) block2 block3

theorem join_1_0 : (twinPrimeSegment 393261 524333).card = 999 := by
  simpa using combineTwinPrimeSegments (by decide : 393261 ≤ 458797)
    (by decide : 458797 ≤ 524333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393261 524333).card = 999 := join_1_0

end S000C03
end Sude.GeneratedTwinScan
