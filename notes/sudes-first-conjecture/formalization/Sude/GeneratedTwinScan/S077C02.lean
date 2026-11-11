import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12719)) 161742893 161775661 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161742893 161775661).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12719 161742893 161775661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12720)) 161775661 161808429 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161775661 161808429).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12720 161775661 161808429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12721)) 161808429 161841197 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161808429 161841197).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12721 161808429 161841197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12722)) 161841197 161873965 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161841197 161873965).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12722 161841197 161873965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161742893 161808429).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 161742893 ≤ 161775661)
    (by decide : 161775661 ≤ 161808429) block0 block1

theorem join_0_1 : (twinPrimeSegment 161808429 161873965).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 161808429 ≤ 161841197)
    (by decide : 161841197 ≤ 161873965) block2 block3

theorem join_1_0 : (twinPrimeSegment 161742893 161873965).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 161742893 ≤ 161808429)
    (by decide : 161808429 ≤ 161873965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161742893 161873965).card = 480 := join_1_0

end S077C02
end Sude.GeneratedTwinScan
