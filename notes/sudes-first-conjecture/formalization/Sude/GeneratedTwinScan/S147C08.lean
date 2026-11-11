import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17588)) 309329965 309362733 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 309329965 309362733).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17588 309329965 309362733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17589)) 309362733 309395501 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 309362733 309395501).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17589 309362733 309395501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17590)) 309395501 309428269 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 309395501 309428269).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17590 309395501 309428269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17591)) 309428269 309461037 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 309428269 309461037).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17591 309428269 309461037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 309329965 309395501).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 309329965 ≤ 309362733)
    (by decide : 309362733 ≤ 309395501) block0 block1

theorem join_0_1 : (twinPrimeSegment 309395501 309461037).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 309395501 ≤ 309428269)
    (by decide : 309428269 ≤ 309461037) block2 block3

theorem join_1_0 : (twinPrimeSegment 309329965 309461037).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 309329965 ≤ 309395501)
    (by decide : 309395501 ≤ 309461037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 309329965 309461037).card = 436 := join_1_0

end S147C08
end Sude.GeneratedTwinScan
