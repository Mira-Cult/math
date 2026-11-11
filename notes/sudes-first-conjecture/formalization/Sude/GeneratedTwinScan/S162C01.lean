import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18436)) 339869741 339902509 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 339869741 339902509).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18436 339869741 339902509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18437)) 339902509 339935277 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 339902509 339935277).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18437 339902509 339935277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18438)) 339935277 339968045 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 339935277 339968045).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18438 339935277 339968045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18439)) 339968045 340000813 = 89 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 339968045 340000813).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18439 339968045 340000813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 339869741 339935277).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 339869741 ≤ 339902509)
    (by decide : 339902509 ≤ 339935277) block0 block1

theorem join_0_1 : (twinPrimeSegment 339935277 340000813).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 339935277 ≤ 339968045)
    (by decide : 339968045 ≤ 340000813) block2 block3

theorem join_1_0 : (twinPrimeSegment 339869741 340000813).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 339869741 ≤ 339935277)
    (by decide : 339935277 ≤ 340000813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 339869741 340000813).card = 461 := join_1_0

end S162C01
end Sude.GeneratedTwinScan
