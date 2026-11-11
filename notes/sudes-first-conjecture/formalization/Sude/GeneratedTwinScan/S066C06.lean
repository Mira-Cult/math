import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139198509 139231277 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 139198509 139231277).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139198509 139231277
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139231277 139264045 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 139231277 139264045).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139231277 139264045
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139264045 139296813 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 139264045 139296813).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139264045 139296813
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 139296813 139329581 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 139296813 139329581).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 139296813 139329581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 139198509 139264045).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 139198509 ≤ 139231277)
    (by decide : 139231277 ≤ 139264045) block0 block1

theorem join_0_1 : (twinPrimeSegment 139264045 139329581).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 139264045 ≤ 139296813)
    (by decide : 139296813 ≤ 139329581) block2 block3

theorem join_1_0 : (twinPrimeSegment 139198509 139329581).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 139198509 ≤ 139264045)
    (by decide : 139264045 ≤ 139329581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 139198509 139329581).card = 502 := join_1_0

end S066C06
end Sude.GeneratedTwinScan
