import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22016)) 484704301 484737069 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484704301 484737069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22016 484704301 484737069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22017)) 484737069 484769837 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484737069 484769837).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22017 484737069 484769837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22018)) 484769837 484802605 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484769837 484802605).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22018 484769837 484802605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22018)) 484802605 484835373 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484802605 484835373).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22018 484802605 484835373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484704301 484769837).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 484704301 ≤ 484737069)
    (by decide : 484737069 ≤ 484769837) block0 block1

theorem join_0_1 : (twinPrimeSegment 484769837 484835373).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 484769837 ≤ 484802605)
    (by decide : 484802605 ≤ 484835373) block2 block3

theorem join_1_0 : (twinPrimeSegment 484704301 484835373).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 484704301 ≤ 484769837)
    (by decide : 484769837 ≤ 484835373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484704301 484835373).card = 448 := join_1_0

end S231C02
end Sude.GeneratedTwinScan
