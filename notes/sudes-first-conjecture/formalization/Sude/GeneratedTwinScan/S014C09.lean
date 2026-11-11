import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 30539821 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 30539821 30572589).card = 134 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30539821 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30539821 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30539821 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 30572589 widths1 = 155 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 30572589 30605357).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30572589 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30572589 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30572589 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 30605357 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 30605357 30638125).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30605357 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30605357 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30605357 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 30638125 widths3 = 154 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 30638125 30670893).card = 154 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30638125 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30638125 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30638125 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 30539821 30605357).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 30539821 ≤ 30572589)
    (by decide : 30572589 ≤ 30605357) block0 block1

theorem join_0_1 : (twinPrimeSegment 30605357 30670893).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 30605357 ≤ 30638125)
    (by decide : 30638125 ≤ 30670893) block2 block3

theorem join_1_0 : (twinPrimeSegment 30539821 30670893).card = 584 := by
  simpa using combineTwinPrimeSegments (by decide : 30539821 ≤ 30605357)
    (by decide : 30605357 ≤ 30670893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 30539821 30670893).card = 584 := join_1_0

end S014C09
end Sude.GeneratedTwinScan
