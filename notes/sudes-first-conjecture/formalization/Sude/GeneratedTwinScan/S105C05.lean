import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14862)) 220856365 220889133 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220856365 220889133).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14862 220856365 220889133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14863)) 220889133 220921901 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220889133 220921901).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14863 220889133 220921901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14864)) 220921901 220954669 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220921901 220954669).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14864 220921901 220954669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14865)) 220954669 220987437 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220954669 220987437).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14865 220954669 220987437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220856365 220921901).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 220856365 ≤ 220889133)
    (by decide : 220889133 ≤ 220921901) block0 block1

theorem join_0_1 : (twinPrimeSegment 220921901 220987437).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 220921901 ≤ 220954669)
    (by decide : 220954669 ≤ 220987437) block2 block3

theorem join_1_0 : (twinPrimeSegment 220856365 220987437).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 220856365 ≤ 220921901)
    (by decide : 220921901 ≤ 220987437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220856365 220987437).card = 461 := join_1_0

end S105C05
end Sude.GeneratedTwinScan
