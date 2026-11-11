import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19164)) 367263789 367296557 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 367263789 367296557).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19164 367263789 367296557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19165)) 367296557 367329325 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 367296557 367329325).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19165 367296557 367329325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19166)) 367329325 367362093 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 367329325 367362093).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19166 367329325 367362093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19167)) 367362093 367394861 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 367362093 367394861).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19167 367362093 367394861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 367263789 367329325).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 367263789 ≤ 367296557)
    (by decide : 367296557 ≤ 367329325) block0 block1

theorem join_0_1 : (twinPrimeSegment 367329325 367394861).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 367329325 ≤ 367362093)
    (by decide : 367362093 ≤ 367394861) block2 block3

theorem join_1_0 : (twinPrimeSegment 367263789 367394861).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 367263789 ≤ 367329325)
    (by decide : 367329325 ≤ 367394861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 367263789 367394861).card = 440 := join_1_0

end S175C02
end Sude.GeneratedTwinScan
