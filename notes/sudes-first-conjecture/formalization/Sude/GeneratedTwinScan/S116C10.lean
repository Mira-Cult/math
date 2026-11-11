import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15640)) 244580397 244613165 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 244580397 244613165).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15640 244580397 244613165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15641)) 244613165 244645933 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 244613165 244645933).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15641 244613165 244645933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15642)) 244645933 244678701 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 244645933 244678701).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15642 244645933 244678701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15643)) 244678701 244711469 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 244678701 244711469).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15643 244678701 244711469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 244580397 244645933).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 244580397 ≤ 244613165)
    (by decide : 244613165 ≤ 244645933) block0 block1

theorem join_0_1 : (twinPrimeSegment 244645933 244711469).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 244645933 ≤ 244678701)
    (by decide : 244678701 ≤ 244711469) block2 block3

theorem join_1_0 : (twinPrimeSegment 244580397 244711469).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 244580397 ≤ 244645933)
    (by decide : 244645933 ≤ 244711469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 244580397 244711469).card = 466 := join_1_0

end S116C10
end Sude.GeneratedTwinScan
