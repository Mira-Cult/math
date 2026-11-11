import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S176C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19233)) 369885229 369917997 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 369885229 369917997).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19233 369885229 369917997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19234)) 369917997 369950765 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 369917997 369950765).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19234 369917997 369950765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19234)) 369950765 369983533 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 369950765 369983533).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19234 369950765 369983533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19235)) 369983533 370016301 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 369983533 370016301).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19235 369983533 370016301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 369885229 369950765).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 369885229 ≤ 369917997)
    (by decide : 369917997 ≤ 369950765) block0 block1

theorem join_0_1 : (twinPrimeSegment 369950765 370016301).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 369950765 ≤ 369983533)
    (by decide : 369983533 ≤ 370016301) block2 block3

theorem join_1_0 : (twinPrimeSegment 369885229 370016301).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 369885229 ≤ 369950765)
    (by decide : 369950765 ≤ 370016301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 369885229 370016301).card = 455 := join_1_0

end S176C06
end Sude.GeneratedTwinScan
