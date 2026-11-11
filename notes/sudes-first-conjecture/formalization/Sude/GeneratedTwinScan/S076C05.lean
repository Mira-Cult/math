import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12651)) 160038957 160071725 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160038957 160071725).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12651 160038957 160071725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12653)) 160071725 160104493 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160071725 160104493).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12653 160071725 160104493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12654)) 160104493 160137261 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160104493 160137261).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12654 160104493 160137261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12655)) 160137261 160170029 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160137261 160170029).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12655 160137261 160170029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160038957 160104493).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 160038957 ≤ 160071725)
    (by decide : 160071725 ≤ 160104493) block0 block1

theorem join_0_1 : (twinPrimeSegment 160104493 160170029).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 160104493 ≤ 160137261)
    (by decide : 160137261 ≤ 160170029) block2 block3

theorem join_1_0 : (twinPrimeSegment 160038957 160170029).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 160038957 ≤ 160104493)
    (by decide : 160104493 ≤ 160170029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160038957 160170029).card = 462 := join_1_0

end S076C05
end Sude.GeneratedTwinScan
