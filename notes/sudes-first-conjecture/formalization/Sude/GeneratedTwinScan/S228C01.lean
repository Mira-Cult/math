import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21870)) 478281773 478314541 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 478281773 478314541).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21870 478281773 478314541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21871)) 478314541 478347309 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 478314541 478347309).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21871 478314541 478347309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21871)) 478347309 478380077 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 478347309 478380077).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21871 478347309 478380077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21872)) 478380077 478412845 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 478380077 478412845).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21872 478380077 478412845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 478281773 478347309).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 478281773 ≤ 478314541)
    (by decide : 478314541 ≤ 478347309) block0 block1

theorem join_0_1 : (twinPrimeSegment 478347309 478412845).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 478347309 ≤ 478380077)
    (by decide : 478380077 ≤ 478412845) block2 block3

theorem join_1_0 : (twinPrimeSegment 478281773 478412845).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 478281773 ≤ 478347309)
    (by decide : 478347309 ≤ 478412845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 478281773 478412845).card = 439 := join_1_0

end S228C01
end Sude.GeneratedTwinScan
