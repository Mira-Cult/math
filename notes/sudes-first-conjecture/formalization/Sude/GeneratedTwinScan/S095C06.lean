import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14143)) 200015917 200048685 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 200015917 200048685).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14143 200015917 200048685
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14145)) 200048685 200081453 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 200048685 200081453).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14145 200048685 200081453
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14146)) 200081453 200114221 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 200081453 200114221).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14146 200081453 200114221
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14147)) 200114221 200146989 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 200114221 200146989).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14147 200114221 200146989
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 200015917 200081453).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 200015917 ≤ 200048685)
    (by decide : 200048685 ≤ 200081453) block0 block1

theorem join_0_1 : (twinPrimeSegment 200081453 200146989).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 200081453 ≤ 200114221)
    (by decide : 200114221 ≤ 200146989) block2 block3

theorem join_1_0 : (twinPrimeSegment 200015917 200146989).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 200015917 ≤ 200081453)
    (by decide : 200081453 ≤ 200146989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 200015917 200146989).card = 479 := join_1_0

end S095C06
end Sude.GeneratedTwinScan
