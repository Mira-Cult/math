import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18962)) 359530541 359563309 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359530541 359563309).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18962 359530541 359563309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18963)) 359563309 359596077 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359563309 359596077).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18963 359563309 359596077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18963)) 359596077 359628845 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359596077 359628845).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18963 359596077 359628845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18964)) 359628845 359661613 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359628845 359661613).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18964 359628845 359661613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359530541 359596077).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 359530541 ≤ 359563309)
    (by decide : 359563309 ≤ 359596077) block0 block1

theorem join_0_1 : (twinPrimeSegment 359596077 359661613).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 359596077 ≤ 359628845)
    (by decide : 359628845 ≤ 359661613) block2 block3

theorem join_1_0 : (twinPrimeSegment 359530541 359661613).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 359530541 ≤ 359596077)
    (by decide : 359596077 ≤ 359661613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359530541 359661613).card = 437 := join_1_0

end S171C07
end Sude.GeneratedTwinScan
