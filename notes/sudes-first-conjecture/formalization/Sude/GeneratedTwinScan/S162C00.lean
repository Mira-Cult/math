import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18432)) 339738669 339771437 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 339738669 339771437).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18432 339738669 339771437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18433)) 339771437 339804205 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 339771437 339804205).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18433 339771437 339804205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18434)) 339804205 339836973 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 339804205 339836973).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18434 339804205 339836973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18435)) 339836973 339869741 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 339836973 339869741).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18435 339836973 339869741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 339738669 339804205).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 339771437)
    (by decide : 339771437 ≤ 339804205) block0 block1

theorem join_0_1 : (twinPrimeSegment 339804205 339869741).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 339804205 ≤ 339836973)
    (by decide : 339836973 ≤ 339869741) block2 block3

theorem join_1_0 : (twinPrimeSegment 339738669 339869741).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 339804205)
    (by decide : 339804205 ≤ 339869741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 339738669 339869741).card = 431 := join_1_0

end S162C00
end Sude.GeneratedTwinScan
