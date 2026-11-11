import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18081)) 326893613 326926381 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 326893613 326926381).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18081 326893613 326926381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18082)) 326926381 326959149 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326926381 326959149).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18082 326926381 326959149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18082)) 326959149 326991917 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326959149 326991917).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18082 326959149 326991917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18083)) 326991917 327024685 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326991917 327024685).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18083 326991917 327024685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 326893613 326959149).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 326893613 ≤ 326926381)
    (by decide : 326926381 ≤ 326959149) block0 block1

theorem join_0_1 : (twinPrimeSegment 326959149 327024685).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 326959149 ≤ 326991917)
    (by decide : 326991917 ≤ 327024685) block2 block3

theorem join_1_0 : (twinPrimeSegment 326893613 327024685).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 326893613 ≤ 326959149)
    (by decide : 326959149 ≤ 327024685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 326893613 327024685).card = 463 := join_1_0

end S155C14
end Sude.GeneratedTwinScan
