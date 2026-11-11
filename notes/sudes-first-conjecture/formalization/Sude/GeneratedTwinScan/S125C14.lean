import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S125C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16248)) 263979053 264011821 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 263979053 264011821).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16248 263979053 264011821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16249)) 264011821 264044589 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 264011821 264044589).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16249 264011821 264044589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16250)) 264044589 264077357 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 264044589 264077357).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16250 264044589 264077357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16251)) 264077357 264110125 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 264077357 264110125).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16251 264077357 264110125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 263979053 264044589).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 263979053 ≤ 264011821)
    (by decide : 264011821 ≤ 264044589) block0 block1

theorem join_0_1 : (twinPrimeSegment 264044589 264110125).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 264044589 ≤ 264077357)
    (by decide : 264077357 ≤ 264110125) block2 block3

theorem join_1_0 : (twinPrimeSegment 263979053 264110125).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 263979053 ≤ 264044589)
    (by decide : 264044589 ≤ 264110125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 263979053 264110125).card = 446 := join_1_0

end S125C14
end Sude.GeneratedTwinScan
