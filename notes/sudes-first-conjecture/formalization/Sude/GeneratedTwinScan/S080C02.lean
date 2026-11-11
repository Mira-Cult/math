import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12964)) 168034349 168067117 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168034349 168067117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12964 168034349 168067117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12965)) 168067117 168099885 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168067117 168099885).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12965 168067117 168099885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12966)) 168099885 168132653 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168099885 168132653).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12966 168099885 168132653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12967)) 168132653 168165421 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168132653 168165421).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12967 168132653 168165421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168034349 168099885).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 168034349 ≤ 168067117)
    (by decide : 168067117 ≤ 168099885) block0 block1

theorem join_0_1 : (twinPrimeSegment 168099885 168165421).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 168099885 ≤ 168132653)
    (by decide : 168132653 ≤ 168165421) block2 block3

theorem join_1_0 : (twinPrimeSegment 168034349 168165421).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 168034349 ≤ 168099885)
    (by decide : 168099885 ≤ 168165421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168034349 168165421).card = 474 := join_1_0

end S080C02
end Sude.GeneratedTwinScan
