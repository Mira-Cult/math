import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21067)) 443809837 443842605 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 443809837 443842605).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21067 443809837 443842605
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21068)) 443842605 443875373 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 443842605 443875373).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21068 443842605 443875373
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21069)) 443875373 443908141 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 443875373 443908141).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21069 443875373 443908141
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21069)) 443908141 443940909 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 443908141 443940909).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21069 443908141 443940909
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 443809837 443875373).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 443809837 ≤ 443842605)
    (by decide : 443842605 ≤ 443875373) block0 block1

theorem join_0_1 : (twinPrimeSegment 443875373 443940909).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 443875373 ≤ 443908141)
    (by decide : 443908141 ≤ 443940909) block2 block3

theorem join_1_0 : (twinPrimeSegment 443809837 443940909).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 443809837 ≤ 443875373)
    (by decide : 443875373 ≤ 443940909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 443809837 443940909).card = 461 := join_1_0

end S211C10
end Sude.GeneratedTwinScan
