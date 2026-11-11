import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S074C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12469)) 155451437 155484205 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 155451437 155484205).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12469 155451437 155484205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12470)) 155484205 155516973 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 155484205 155516973).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12470 155484205 155516973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12471)) 155516973 155549741 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 155516973 155549741).card = 145 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12471 155516973 155549741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12473)) 155549741 155582509 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 155549741 155582509).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12473 155549741 155582509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 155451437 155516973).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 155451437 ≤ 155484205)
    (by decide : 155484205 ≤ 155516973) block0 block1

theorem join_0_1 : (twinPrimeSegment 155516973 155582509).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 155516973 ≤ 155549741)
    (by decide : 155549741 ≤ 155582509) block2 block3

theorem join_1_0 : (twinPrimeSegment 155451437 155582509).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 155451437 ≤ 155516973)
    (by decide : 155516973 ≤ 155582509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 155451437 155582509).card = 513 := join_1_0

end S074C02
end Sude.GeneratedTwinScan
