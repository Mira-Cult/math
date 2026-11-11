import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19158)) 367001645 367034413 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 367001645 367034413).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19158 367001645 367034413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19158)) 367034413 367067181 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 367034413 367067181).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19158 367034413 367067181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19159)) 367067181 367099949 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 367067181 367099949).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19159 367067181 367099949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19160)) 367099949 367132717 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 367099949 367132717).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19160 367099949 367132717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 367001645 367067181).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 367001645 ≤ 367034413)
    (by decide : 367034413 ≤ 367067181) block0 block1

theorem join_0_1 : (twinPrimeSegment 367067181 367132717).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 367067181 ≤ 367099949)
    (by decide : 367099949 ≤ 367132717) block2 block3

theorem join_1_0 : (twinPrimeSegment 367001645 367132717).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 367001645 ≤ 367067181)
    (by decide : 367067181 ≤ 367132717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 367001645 367132717).card = 439 := join_1_0

end S175C00
end Sude.GeneratedTwinScan
