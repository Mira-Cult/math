import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 9306157 widths0 = 173 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 9306157 9338925).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9306157 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9306157 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9306157 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 9338925 widths1 = 179 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 9338925 9371693).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9338925 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9338925 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9338925 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 9371693 widths2 = 161 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 9371693 9404461).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9371693 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9371693 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9371693 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 9404461 widths3 = 155 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 9404461 9437229).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9404461 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9404461 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9404461 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 9306157 9371693).card = 352 := by
  simpa using combineTwinPrimeSegments (by decide : 9306157 ≤ 9338925)
    (by decide : 9338925 ≤ 9371693) block0 block1

theorem join_0_1 : (twinPrimeSegment 9371693 9437229).card = 316 := by
  simpa using combineTwinPrimeSegments (by decide : 9371693 ≤ 9404461)
    (by decide : 9404461 ≤ 9437229) block2 block3

theorem join_1_0 : (twinPrimeSegment 9306157 9437229).card = 668 := by
  simpa using combineTwinPrimeSegments (by decide : 9306157 ≤ 9371693)
    (by decide : 9371693 ≤ 9437229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 9306157 9437229).card = 668 := join_1_0

end S004C07
end Sude.GeneratedTwinScan
