import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21632)) 467927085 467959853 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 467927085 467959853).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21632 467927085 467959853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21633)) 467959853 467992621 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 467959853 467992621).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21633 467959853 467992621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21633)) 467992621 468025389 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 467992621 468025389).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21633 467992621 468025389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21634)) 468025389 468058157 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468025389 468058157).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21634 468025389 468058157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 467927085 467992621).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 467927085 ≤ 467959853)
    (by decide : 467959853 ≤ 467992621) block0 block1

theorem join_0_1 : (twinPrimeSegment 467992621 468058157).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 467992621 ≤ 468025389)
    (by decide : 468025389 ≤ 468058157) block2 block3

theorem join_1_0 : (twinPrimeSegment 467927085 468058157).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 467927085 ≤ 467992621)
    (by decide : 467992621 ≤ 468058157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 467927085 468058157).card = 401 := join_1_0

end S223C02
end Sude.GeneratedTwinScan
