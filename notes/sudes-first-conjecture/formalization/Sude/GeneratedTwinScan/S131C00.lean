import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16575)) 274726957 274759725 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274726957 274759725).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16575 274726957 274759725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16576)) 274759725 274792493 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274759725 274792493).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16576 274759725 274792493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16577)) 274792493 274825261 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274792493 274825261).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16577 274792493 274825261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16578)) 274825261 274858029 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274825261 274858029).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16578 274825261 274858029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274726957 274792493).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 274726957 ≤ 274759725)
    (by decide : 274759725 ≤ 274792493) block0 block1

theorem join_0_1 : (twinPrimeSegment 274792493 274858029).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 274792493 ≤ 274825261)
    (by decide : 274825261 ≤ 274858029) block2 block3

theorem join_1_0 : (twinPrimeSegment 274726957 274858029).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 274726957 ≤ 274792493)
    (by decide : 274792493 ≤ 274858029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274726957 274858029).card = 449 := join_1_0

end S131C00
end Sude.GeneratedTwinScan
