import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17420)) 303431725 303464493 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303431725 303464493).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17420 303431725 303464493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17421)) 303464493 303497261 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303464493 303497261).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17421 303464493 303497261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17422)) 303497261 303530029 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 303497261 303530029).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17422 303497261 303530029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17423)) 303530029 303562797 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303530029 303562797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17423 303530029 303562797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303431725 303497261).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 303431725 ≤ 303464493)
    (by decide : 303464493 ≤ 303497261) block0 block1

theorem join_0_1 : (twinPrimeSegment 303497261 303562797).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 303497261 ≤ 303530029)
    (by decide : 303530029 ≤ 303562797) block2 block3

theorem join_1_0 : (twinPrimeSegment 303431725 303562797).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 303431725 ≤ 303497261)
    (by decide : 303497261 ≤ 303562797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303431725 303562797).card = 461 := join_1_0

end S144C11
end Sude.GeneratedTwinScan
