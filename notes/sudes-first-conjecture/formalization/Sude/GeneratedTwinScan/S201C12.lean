import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20570)) 423100461 423133229 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423100461 423133229).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20570 423100461 423133229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20570)) 423133229 423165997 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423133229 423165997).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20570 423133229 423165997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20571)) 423165997 423198765 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423165997 423198765).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20571 423165997 423198765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20572)) 423198765 423231533 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423198765 423231533).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20572 423198765 423231533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423100461 423165997).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 423100461 ≤ 423133229)
    (by decide : 423133229 ≤ 423165997) block0 block1

theorem join_0_1 : (twinPrimeSegment 423165997 423231533).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 423165997 ≤ 423198765)
    (by decide : 423198765 ≤ 423231533) block2 block3

theorem join_1_0 : (twinPrimeSegment 423100461 423231533).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 423100461 ≤ 423165997)
    (by decide : 423165997 ≤ 423231533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423100461 423231533).card = 431 := join_1_0

end S201C12
end Sude.GeneratedTwinScan
