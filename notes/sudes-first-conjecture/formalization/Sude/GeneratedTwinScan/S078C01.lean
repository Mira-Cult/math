import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12796)) 163708973 163741741 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163708973 163741741).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12796 163708973 163741741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12797)) 163741741 163774509 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163741741 163774509).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12797 163741741 163774509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12798)) 163774509 163807277 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 163774509 163807277).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12798 163774509 163807277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12800)) 163807277 163840045 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163807277 163840045).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12800 163807277 163840045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163708973 163774509).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 163708973 ≤ 163741741)
    (by decide : 163741741 ≤ 163774509) block0 block1

theorem join_0_1 : (twinPrimeSegment 163774509 163840045).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 163774509 ≤ 163807277)
    (by decide : 163807277 ≤ 163840045) block2 block3

theorem join_1_0 : (twinPrimeSegment 163708973 163840045).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 163708973 ≤ 163774509)
    (by decide : 163774509 ≤ 163840045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163708973 163840045).card = 464 := join_1_0

end S078C01
end Sude.GeneratedTwinScan
