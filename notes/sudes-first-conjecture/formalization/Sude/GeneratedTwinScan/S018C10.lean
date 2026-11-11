import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39059501 widths0 = 149 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 39059501 39092269).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39059501 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39092269 widths1 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 39092269 39125037).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39092269 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39125037 widths2 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 39125037 39157805).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39125037 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39157805 widths3 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 39157805 39190573).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39157805 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 39059501 39125037).card = 300 := by
  simpa using combineTwinPrimeSegments (by decide : 39059501 ≤ 39092269)
    (by decide : 39092269 ≤ 39125037) block0 block1

theorem join_0_1 : (twinPrimeSegment 39125037 39190573).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 39125037 ≤ 39157805)
    (by decide : 39157805 ≤ 39190573) block2 block3

theorem join_1_0 : (twinPrimeSegment 39059501 39190573).card = 557 := by
  simpa using combineTwinPrimeSegments (by decide : 39059501 ≤ 39125037)
    (by decide : 39125037 ≤ 39190573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 39059501 39190573).card = 557 := join_1_0

end S018C10
end Sude.GeneratedTwinScan
