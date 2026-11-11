import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18553)) 344195117 344227885 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344195117 344227885).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18553 344195117 344227885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18554)) 344227885 344260653 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344227885 344260653).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18554 344227885 344260653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18555)) 344260653 344293421 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344260653 344293421).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18555 344260653 344293421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18556)) 344293421 344326189 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344293421 344326189).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18556 344293421 344326189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344195117 344260653).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 344195117 ≤ 344227885)
    (by decide : 344227885 ≤ 344260653) block0 block1

theorem join_0_1 : (twinPrimeSegment 344260653 344326189).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 344260653 ≤ 344293421)
    (by decide : 344293421 ≤ 344326189) block2 block3

theorem join_1_0 : (twinPrimeSegment 344195117 344326189).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 344195117 ≤ 344260653)
    (by decide : 344260653 ≤ 344326189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344195117 344326189).card = 471 := join_1_0

end S164C02
end Sude.GeneratedTwinScan
