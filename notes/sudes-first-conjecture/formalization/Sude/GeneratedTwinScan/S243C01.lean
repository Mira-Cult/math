import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22578)) 509739053 509771821 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509739053 509771821).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22578 509739053 509771821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22578)) 509771821 509804589 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509771821 509804589).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22578 509771821 509804589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22579)) 509804589 509837357 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509804589 509837357).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22579 509804589 509837357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22580)) 509837357 509870125 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509837357 509870125).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22580 509837357 509870125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509739053 509804589).card = 192 := by
  simpa using combineTwinPrimeSegments (by decide : 509739053 ≤ 509771821)
    (by decide : 509771821 ≤ 509804589) block0 block1

theorem join_0_1 : (twinPrimeSegment 509804589 509870125).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 509804589 ≤ 509837357)
    (by decide : 509837357 ≤ 509870125) block2 block3

theorem join_1_0 : (twinPrimeSegment 509739053 509870125).card = 388 := by
  simpa using combineTwinPrimeSegments (by decide : 509739053 ≤ 509804589)
    (by decide : 509804589 ≤ 509870125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509739053 509870125).card = 388 := join_1_0

end S243C01
end Sude.GeneratedTwinScan
