import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21656)) 468975661 469008429 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468975661 469008429).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21656 468975661 469008429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21657)) 469008429 469041197 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 469008429 469041197).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21657 469008429 469041197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21658)) 469041197 469073965 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 469041197 469073965).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21658 469041197 469073965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21658)) 469073965 469106733 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 469073965 469106733).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21658 469073965 469106733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468975661 469041197).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 468975661 ≤ 469008429)
    (by decide : 469008429 ≤ 469041197) block0 block1

theorem join_0_1 : (twinPrimeSegment 469041197 469106733).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 469041197 ≤ 469073965)
    (by decide : 469073965 ≤ 469106733) block2 block3

theorem join_1_0 : (twinPrimeSegment 468975661 469106733).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 468975661 ≤ 469041197)
    (by decide : 469041197 ≤ 469106733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468975661 469106733).card = 421 := join_1_0

end S223C10
end Sude.GeneratedTwinScan
