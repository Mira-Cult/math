import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17423)) 303562797 303595565 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 303562797 303595565).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17423 303562797 303595565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17424)) 303595565 303628333 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 303595565 303628333).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17424 303595565 303628333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17425)) 303628333 303661101 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 303628333 303661101).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17425 303628333 303661101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17426)) 303661101 303693869 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 303661101 303693869).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17426 303661101 303693869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 303562797 303628333).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 303562797 ≤ 303595565)
    (by decide : 303595565 ≤ 303628333) block0 block1

theorem join_0_1 : (twinPrimeSegment 303628333 303693869).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 303628333 ≤ 303661101)
    (by decide : 303661101 ≤ 303693869) block2 block3

theorem join_1_0 : (twinPrimeSegment 303562797 303693869).card = 412 := by
  simpa using combineTwinPrimeSegments (by decide : 303562797 ≤ 303628333)
    (by decide : 303628333 ≤ 303693869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 303562797 303693869).card = 412 := join_1_0

end S144C12
end Sude.GeneratedTwinScan
