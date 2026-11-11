import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16900)) 285605933 285638701 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 285605933 285638701).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16900 285605933 285638701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16901)) 285638701 285671469 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 285638701 285671469).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16901 285638701 285671469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16902)) 285671469 285704237 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 285671469 285704237).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16902 285671469 285704237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16903)) 285704237 285737005 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 285704237 285737005).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16903 285704237 285737005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 285605933 285671469).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 285605933 ≤ 285638701)
    (by decide : 285638701 ≤ 285671469) block0 block1

theorem join_0_1 : (twinPrimeSegment 285671469 285737005).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 285671469 ≤ 285704237)
    (by decide : 285704237 ≤ 285737005) block2 block3

theorem join_1_0 : (twinPrimeSegment 285605933 285737005).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 285605933 ≤ 285671469)
    (by decide : 285671469 ≤ 285737005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 285605933 285737005).card = 477 := join_1_0

end S136C03
end Sude.GeneratedTwinScan
