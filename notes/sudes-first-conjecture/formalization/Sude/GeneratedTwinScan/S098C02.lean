import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14346)) 205783085 205815853 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205783085 205815853).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14346 205783085 205815853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14347)) 205815853 205848621 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205815853 205848621).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14347 205815853 205848621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14348)) 205848621 205881389 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205848621 205881389).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14348 205848621 205881389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14349)) 205881389 205914157 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205881389 205914157).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14349 205881389 205914157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205783085 205848621).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 205783085 ≤ 205815853)
    (by decide : 205815853 ≤ 205848621) block0 block1

theorem join_0_1 : (twinPrimeSegment 205848621 205914157).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 205848621 ≤ 205881389)
    (by decide : 205881389 ≤ 205914157) block2 block3

theorem join_1_0 : (twinPrimeSegment 205783085 205914157).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 205783085 ≤ 205848621)
    (by decide : 205848621 ≤ 205914157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205783085 205914157).card = 480 := join_1_0

end S098C02
end Sude.GeneratedTwinScan
