import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22719)) 516161581 516194349 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516161581 516194349).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22719 516161581 516194349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22720)) 516194349 516227117 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516194349 516227117).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22720 516194349 516227117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22721)) 516227117 516259885 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 516227117 516259885).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22721 516227117 516259885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22722)) 516259885 516292653 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 516259885 516292653).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22722 516259885 516292653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516161581 516227117).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 516161581 ≤ 516194349)
    (by decide : 516194349 ≤ 516227117) block0 block1

theorem join_0_1 : (twinPrimeSegment 516227117 516292653).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 516227117 ≤ 516259885)
    (by decide : 516259885 ≤ 516292653) block2 block3

theorem join_1_0 : (twinPrimeSegment 516161581 516292653).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 516161581 ≤ 516227117)
    (by decide : 516227117 ≤ 516292653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516161581 516292653).card = 429 := join_1_0

end S246C02
end Sude.GeneratedTwinScan
