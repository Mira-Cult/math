import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18965)) 359661613 359694381 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359661613 359694381).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18965 359661613 359694381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18966)) 359694381 359727149 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359694381 359727149).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18966 359694381 359727149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18967)) 359727149 359759917 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359727149 359759917).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18967 359727149 359759917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18968)) 359759917 359792685 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359759917 359792685).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18968 359759917 359792685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359661613 359727149).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 359661613 ≤ 359694381)
    (by decide : 359694381 ≤ 359727149) block0 block1

theorem join_0_1 : (twinPrimeSegment 359727149 359792685).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 359727149 ≤ 359759917)
    (by decide : 359759917 ≤ 359792685) block2 block3

theorem join_1_0 : (twinPrimeSegment 359661613 359792685).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 359661613 ≤ 359727149)
    (by decide : 359727149 ≤ 359792685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359661613 359792685).card = 456 := join_1_0

end S171C08
end Sude.GeneratedTwinScan
