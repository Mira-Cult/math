import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149291053 149323821 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149291053 149323821).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149291053 149323821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149323821 149356589 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149323821 149356589).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149323821 149356589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149356589 149389357 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149356589 149389357).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149356589 149389357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149389357 149422125 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149389357 149422125).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149389357 149422125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149291053 149356589).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 149291053 ≤ 149323821)
    (by decide : 149323821 ≤ 149356589) block0 block1

theorem join_0_1 : (twinPrimeSegment 149356589 149422125).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 149356589 ≤ 149389357)
    (by decide : 149389357 ≤ 149422125) block2 block3

theorem join_1_0 : (twinPrimeSegment 149291053 149422125).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 149291053 ≤ 149356589)
    (by decide : 149356589 ≤ 149422125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149291053 149422125).card = 482 := join_1_0

end S071C03
end Sude.GeneratedTwinScan
