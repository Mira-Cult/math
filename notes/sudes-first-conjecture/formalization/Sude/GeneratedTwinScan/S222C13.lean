import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21617)) 467271725 467304493 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 467271725 467304493).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21617 467271725 467304493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21617)) 467304493 467337261 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 467304493 467337261).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21617 467304493 467337261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21618)) 467337261 467370029 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 467337261 467370029).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21618 467337261 467370029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21619)) 467370029 467402797 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 467370029 467402797).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21619 467370029 467402797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 467271725 467337261).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 467271725 ≤ 467304493)
    (by decide : 467304493 ≤ 467337261) block0 block1

theorem join_0_1 : (twinPrimeSegment 467337261 467402797).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 467337261 ≤ 467370029)
    (by decide : 467370029 ≤ 467402797) block2 block3

theorem join_1_0 : (twinPrimeSegment 467271725 467402797).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 467271725 ≤ 467337261)
    (by decide : 467337261 ≤ 467402797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 467271725 467402797).card = 467 := join_1_0

end S222C13
end Sude.GeneratedTwinScan
