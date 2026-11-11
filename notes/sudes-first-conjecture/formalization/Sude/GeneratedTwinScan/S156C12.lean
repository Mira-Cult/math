import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18131)) 328728621 328761389 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 328728621 328761389).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18131 328728621 328761389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18132)) 328761389 328794157 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 328761389 328794157).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18132 328761389 328794157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18133)) 328794157 328826925 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 328794157 328826925).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18133 328794157 328826925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18134)) 328826925 328859693 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 328826925 328859693).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18134 328826925 328859693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 328728621 328794157).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 328728621 ≤ 328761389)
    (by decide : 328761389 ≤ 328794157) block0 block1

theorem join_0_1 : (twinPrimeSegment 328794157 328859693).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 328794157 ≤ 328826925)
    (by decide : 328826925 ≤ 328859693) block2 block3

theorem join_1_0 : (twinPrimeSegment 328728621 328859693).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 328728621 ≤ 328794157)
    (by decide : 328794157 ≤ 328859693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 328728621 328859693).card = 467 := join_1_0

end S156C12
end Sude.GeneratedTwinScan
