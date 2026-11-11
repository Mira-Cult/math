import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59113517 59146285 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 59113517 59146285).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59113517 59146285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59146285 59179053 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59146285 59179053).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59146285 59179053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59179053 59211821 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59179053 59211821).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59179053 59211821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59211821 59244589 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59211821 59244589).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59211821 59244589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 59113517 59179053).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 59113517 ≤ 59146285)
    (by decide : 59146285 ≤ 59179053) block0 block1

theorem join_0_1 : (twinPrimeSegment 59179053 59244589).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 59179053 ≤ 59211821)
    (by decide : 59211821 ≤ 59244589) block2 block3

theorem join_1_0 : (twinPrimeSegment 59113517 59244589).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 59113517 ≤ 59179053)
    (by decide : 59179053 ≤ 59244589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 59113517 59244589).card = 520 := join_1_0

end S028C03
end Sude.GeneratedTwinScan
