import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18383)) 337903661 337936429 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 337903661 337936429).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18383 337903661 337936429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18383)) 337936429 337969197 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 337936429 337969197).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18383 337936429 337969197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18384)) 337969197 338001965 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 337969197 338001965).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18384 337969197 338001965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18385)) 338001965 338034733 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 338001965 338034733).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18385 338001965 338034733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 337903661 337969197).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 337903661 ≤ 337936429)
    (by decide : 337936429 ≤ 337969197) block0 block1

theorem join_0_1 : (twinPrimeSegment 337969197 338034733).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 337969197 ≤ 338001965)
    (by decide : 338001965 ≤ 338034733) block2 block3

theorem join_1_0 : (twinPrimeSegment 337903661 338034733).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 337903661 ≤ 337969197)
    (by decide : 337969197 ≤ 338034733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 337903661 338034733).card = 449 := join_1_0

end S161C02
end Sude.GeneratedTwinScan
