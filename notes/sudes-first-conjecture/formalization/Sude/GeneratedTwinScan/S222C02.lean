import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21583)) 465829933 465862701 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465829933 465862701).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21583 465829933 465862701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21584)) 465862701 465895469 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465862701 465895469).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21584 465862701 465895469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21585)) 465895469 465928237 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 465895469 465928237).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21585 465895469 465928237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21586)) 465928237 465961005 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 465928237 465961005).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21586 465928237 465961005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465829933 465895469).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 465829933 ≤ 465862701)
    (by decide : 465862701 ≤ 465895469) block0 block1

theorem join_0_1 : (twinPrimeSegment 465895469 465961005).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 465895469 ≤ 465928237)
    (by decide : 465928237 ≤ 465961005) block2 block3

theorem join_1_0 : (twinPrimeSegment 465829933 465961005).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 465829933 ≤ 465895469)
    (by decide : 465895469 ≤ 465961005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465829933 465961005).card = 427 := join_1_0

end S222C02
end Sude.GeneratedTwinScan
