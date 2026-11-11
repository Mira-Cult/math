import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104071213 104103981 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 104071213 104103981).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104071213 104103981
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104103981 104136749 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 104103981 104136749).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104103981 104136749
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104136749 104169517 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 104136749 104169517).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104136749 104169517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104169517 104202285 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 104169517 104202285).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104169517 104202285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 104071213 104136749).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 104071213 ≤ 104103981)
    (by decide : 104103981 ≤ 104136749) block0 block1

theorem join_0_1 : (twinPrimeSegment 104136749 104202285).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 104136749 ≤ 104169517)
    (by decide : 104169517 ≤ 104202285) block2 block3

theorem join_1_0 : (twinPrimeSegment 104071213 104202285).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 104071213 ≤ 104136749)
    (by decide : 104136749 ≤ 104202285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 104071213 104202285).card = 515 := join_1_0

end S049C10
end Sude.GeneratedTwinScan
