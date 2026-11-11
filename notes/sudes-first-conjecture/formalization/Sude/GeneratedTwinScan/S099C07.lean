import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S099C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14441)) 208535597 208568365 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 208535597 208568365).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14441 208535597 208568365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14443)) 208568365 208601133 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 208568365 208601133).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14443 208568365 208601133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14444)) 208601133 208633901 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 208601133 208633901).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14444 208601133 208633901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14445)) 208633901 208666669 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 208633901 208666669).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14445 208633901 208666669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 208535597 208601133).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 208535597 ≤ 208568365)
    (by decide : 208568365 ≤ 208601133) block0 block1

theorem join_0_1 : (twinPrimeSegment 208601133 208666669).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 208601133 ≤ 208633901)
    (by decide : 208633901 ≤ 208666669) block2 block3

theorem join_1_0 : (twinPrimeSegment 208535597 208666669).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 208535597 ≤ 208601133)
    (by decide : 208601133 ≤ 208666669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 208535597 208666669).card = 462 := join_1_0

end S099C07
end Sude.GeneratedTwinScan
