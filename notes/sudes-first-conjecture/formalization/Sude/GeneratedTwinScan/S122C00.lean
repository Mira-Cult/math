import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15996)) 255852589 255885357 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255852589 255885357).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15996 255852589 255885357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15997)) 255885357 255918125 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 255885357 255918125).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15997 255885357 255918125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15998)) 255918125 255950893 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255918125 255950893).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15998 255918125 255950893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15999)) 255950893 255983661 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255950893 255983661).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15999 255950893 255983661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255852589 255918125).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 255885357)
    (by decide : 255885357 ≤ 255918125) block0 block1

theorem join_0_1 : (twinPrimeSegment 255918125 255983661).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 255918125 ≤ 255950893)
    (by decide : 255950893 ≤ 255983661) block2 block3

theorem join_1_0 : (twinPrimeSegment 255852589 255983661).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 255918125)
    (by decide : 255918125 ≤ 255983661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255852589 255983661).card = 429 := join_1_0

end S122C00
end Sude.GeneratedTwinScan
