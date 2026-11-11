import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13919)) 193724461 193757229 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193724461 193757229).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13919 193724461 193757229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13920)) 193757229 193789997 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193757229 193789997).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13920 193757229 193789997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13922)) 193789997 193822765 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193789997 193822765).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13922 193789997 193822765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13923)) 193822765 193855533 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193822765 193855533).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13923 193822765 193855533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193724461 193789997).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 193724461 ≤ 193757229)
    (by decide : 193757229 ≤ 193789997) block0 block1

theorem join_0_1 : (twinPrimeSegment 193789997 193855533).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 193789997 ≤ 193822765)
    (by decide : 193822765 ≤ 193855533) block2 block3

theorem join_1_0 : (twinPrimeSegment 193724461 193855533).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 193724461 ≤ 193789997)
    (by decide : 193789997 ≤ 193855533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193724461 193855533).card = 478 := join_1_0

end S092C06
end Sude.GeneratedTwinScan
