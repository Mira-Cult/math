import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S180C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19480)) 379453485 379486253 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 379453485 379486253).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19480 379453485 379486253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19481)) 379486253 379519021 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 379486253 379519021).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19481 379486253 379519021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19482)) 379519021 379551789 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 379519021 379551789).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19482 379519021 379551789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19482)) 379551789 379584557 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 379551789 379584557).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19482 379551789 379584557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 379453485 379519021).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 379453485 ≤ 379486253)
    (by decide : 379486253 ≤ 379519021) block0 block1

theorem join_0_1 : (twinPrimeSegment 379519021 379584557).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 379519021 ≤ 379551789)
    (by decide : 379551789 ≤ 379584557) block2 block3

theorem join_1_0 : (twinPrimeSegment 379453485 379584557).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 379453485 ≤ 379519021)
    (by decide : 379519021 ≤ 379584557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 379453485 379584557).card = 444 := join_1_0

end S180C15
end Sude.GeneratedTwinScan
