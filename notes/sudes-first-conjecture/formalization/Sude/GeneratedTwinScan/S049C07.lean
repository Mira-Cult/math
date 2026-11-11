import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103677997 103710765 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103677997 103710765).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103677997 103710765
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103710765 103743533 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103710765 103743533).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103710765 103743533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103743533 103776301 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 103743533 103776301).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103743533 103776301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103776301 103809069 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 103776301 103809069).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103776301 103809069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103677997 103743533).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 103677997 ≤ 103710765)
    (by decide : 103710765 ≤ 103743533) block0 block1

theorem join_0_1 : (twinPrimeSegment 103743533 103809069).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 103743533 ≤ 103776301)
    (by decide : 103776301 ≤ 103809069) block2 block3

theorem join_1_0 : (twinPrimeSegment 103677997 103809069).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 103677997 ≤ 103743533)
    (by decide : 103743533 ≤ 103809069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103677997 103809069).card = 524 := join_1_0

end S049C07
end Sude.GeneratedTwinScan
