import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22218)) 493617197 493649965 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 493617197 493649965).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22218 493617197 493649965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22218)) 493649965 493682733 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 493649965 493682733).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22218 493649965 493682733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22219)) 493682733 493715501 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 493682733 493715501).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22219 493682733 493715501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22220)) 493715501 493748269 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 493715501 493748269).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22220 493715501 493748269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 493617197 493682733).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 493617197 ≤ 493649965)
    (by decide : 493649965 ≤ 493682733) block0 block1

theorem join_0_1 : (twinPrimeSegment 493682733 493748269).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 493682733 ≤ 493715501)
    (by decide : 493715501 ≤ 493748269) block2 block3

theorem join_1_0 : (twinPrimeSegment 493617197 493748269).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 493617197 ≤ 493682733)
    (by decide : 493682733 ≤ 493748269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 493617197 493748269).card = 420 := join_1_0

end S235C06
end Sude.GeneratedTwinScan
