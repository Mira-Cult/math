import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18903)) 357302317 357335085 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357302317 357335085).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18903 357302317 357335085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18904)) 357335085 357367853 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357335085 357367853).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18904 357335085 357367853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18905)) 357367853 357400621 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357367853 357400621).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18905 357367853 357400621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18905)) 357400621 357433389 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357400621 357433389).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18905 357400621 357433389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357302317 357367853).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 357302317 ≤ 357335085)
    (by decide : 357335085 ≤ 357367853) block0 block1

theorem join_0_1 : (twinPrimeSegment 357367853 357433389).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 357367853 ≤ 357400621)
    (by decide : 357400621 ≤ 357433389) block2 block3

theorem join_1_0 : (twinPrimeSegment 357302317 357433389).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 357302317 ≤ 357367853)
    (by decide : 357367853 ≤ 357433389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357302317 357433389).card = 441 := join_1_0

end S170C06
end Sude.GeneratedTwinScan
