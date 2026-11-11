import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21290)) 453247021 453279789 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453247021 453279789).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21290 453247021 453279789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21291)) 453279789 453312557 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453279789 453312557).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21291 453279789 453312557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21291)) 453312557 453345325 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453312557 453345325).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21291 453312557 453345325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21292)) 453345325 453378093 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453345325 453378093).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21292 453345325 453378093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453247021 453312557).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 453247021 ≤ 453279789)
    (by decide : 453279789 ≤ 453312557) block0 block1

theorem join_0_1 : (twinPrimeSegment 453312557 453378093).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 453312557 ≤ 453345325)
    (by decide : 453345325 ≤ 453378093) block2 block3

theorem join_1_0 : (twinPrimeSegment 453247021 453378093).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 453247021 ≤ 453312557)
    (by decide : 453312557 ≤ 453378093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453247021 453378093).card = 460 := join_1_0

end S216C02
end Sude.GeneratedTwinScan
