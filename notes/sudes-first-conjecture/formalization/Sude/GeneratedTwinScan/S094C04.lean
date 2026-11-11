import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14060)) 197656621 197689389 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197656621 197689389).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14060 197656621 197689389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14061)) 197689389 197722157 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197689389 197722157).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14061 197689389 197722157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14062)) 197722157 197754925 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197722157 197754925).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14062 197722157 197754925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14063)) 197754925 197787693 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197754925 197787693).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14063 197754925 197787693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197656621 197722157).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 197656621 ≤ 197689389)
    (by decide : 197689389 ≤ 197722157) block0 block1

theorem join_0_1 : (twinPrimeSegment 197722157 197787693).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 197722157 ≤ 197754925)
    (by decide : 197754925 ≤ 197787693) block2 block3

theorem join_1_0 : (twinPrimeSegment 197656621 197787693).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 197656621 ≤ 197722157)
    (by decide : 197722157 ≤ 197787693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197656621 197787693).card = 464 := join_1_0

end S094C04
end Sude.GeneratedTwinScan
