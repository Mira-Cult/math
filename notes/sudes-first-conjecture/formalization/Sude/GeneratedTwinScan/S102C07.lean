import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14658)) 214827053 214859821 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214827053 214859821).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14658 214827053 214859821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14659)) 214859821 214892589 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214859821 214892589).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14659 214859821 214892589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14660)) 214892589 214925357 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 214892589 214925357).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14660 214892589 214925357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14661)) 214925357 214958125 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214925357 214958125).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14661 214925357 214958125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214827053 214892589).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 214827053 ≤ 214859821)
    (by decide : 214859821 ≤ 214892589) block0 block1

theorem join_0_1 : (twinPrimeSegment 214892589 214958125).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 214892589 ≤ 214925357)
    (by decide : 214925357 ≤ 214958125) block2 block3

theorem join_1_0 : (twinPrimeSegment 214827053 214958125).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 214827053 ≤ 214892589)
    (by decide : 214892589 ≤ 214958125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214827053 214958125).card = 481 := join_1_0

end S102C07
end Sude.GeneratedTwinScan
