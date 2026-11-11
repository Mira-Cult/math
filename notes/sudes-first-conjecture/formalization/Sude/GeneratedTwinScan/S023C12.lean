import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49807405 widths0 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 49807405 49840173).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49807405 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49840173 widths1 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 49840173 49872941).card = 114 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49840173 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49872941 widths2 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 49872941 49905709).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49872941 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 49905709 widths3 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 49905709 49938477).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 49905709 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 49807405 49872941).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 49807405 ≤ 49840173)
    (by decide : 49840173 ≤ 49872941) block0 block1

theorem join_0_1 : (twinPrimeSegment 49872941 49938477).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 49872941 ≤ 49905709)
    (by decide : 49905709 ≤ 49938477) block2 block3

theorem join_1_0 : (twinPrimeSegment 49807405 49938477).card = 509 := by
  simpa using combineTwinPrimeSegments (by decide : 49807405 ≤ 49872941)
    (by decide : 49872941 ≤ 49938477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 49807405 49938477).card = 509 := join_1_0

end S023C12
end Sude.GeneratedTwinScan
