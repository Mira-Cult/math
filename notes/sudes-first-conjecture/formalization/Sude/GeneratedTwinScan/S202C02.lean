import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S202C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20589)) 423886893 423919661 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 423886893 423919661).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20589 423886893 423919661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20590)) 423919661 423952429 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 423919661 423952429).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20590 423919661 423952429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20590)) 423952429 423985197 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 423952429 423985197).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20590 423952429 423985197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20591)) 423985197 424017965 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 423985197 424017965).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20591 423985197 424017965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 423886893 423952429).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 423886893 ≤ 423919661)
    (by decide : 423919661 ≤ 423952429) block0 block1

theorem join_0_1 : (twinPrimeSegment 423952429 424017965).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 423952429 ≤ 423985197)
    (by decide : 423985197 ≤ 424017965) block2 block3

theorem join_1_0 : (twinPrimeSegment 423886893 424017965).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 423886893 ≤ 423952429)
    (by decide : 423952429 ≤ 424017965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 423886893 424017965).card = 435 := join_1_0

end S202C02
end Sude.GeneratedTwinScan
