import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15585)) 242876461 242909229 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 242876461 242909229).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15585 242876461 242909229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15586)) 242909229 242941997 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 242909229 242941997).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15586 242909229 242941997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15587)) 242941997 242974765 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 242941997 242974765).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15587 242941997 242974765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15588)) 242974765 243007533 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 242974765 243007533).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15588 242974765 243007533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 242876461 242941997).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 242876461 ≤ 242909229)
    (by decide : 242909229 ≤ 242941997) block0 block1

theorem join_0_1 : (twinPrimeSegment 242941997 243007533).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 242941997 ≤ 242974765)
    (by decide : 242974765 ≤ 243007533) block2 block3

theorem join_1_0 : (twinPrimeSegment 242876461 243007533).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 242876461 ≤ 242941997)
    (by decide : 242941997 ≤ 243007533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 242876461 243007533).card = 493 := join_1_0

end S115C13
end Sude.GeneratedTwinScan
