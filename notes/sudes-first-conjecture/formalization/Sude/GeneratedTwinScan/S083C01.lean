import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13199)) 174194733 174227501 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174194733 174227501).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13199 174194733 174227501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13200)) 174227501 174260269 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 174227501 174260269).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13200 174227501 174260269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13202)) 174260269 174293037 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 174260269 174293037).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13202 174260269 174293037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13203)) 174293037 174325805 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174293037 174325805).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13203 174293037 174325805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174194733 174260269).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 174194733 ≤ 174227501)
    (by decide : 174227501 ≤ 174260269) block0 block1

theorem join_0_1 : (twinPrimeSegment 174260269 174325805).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 174260269 ≤ 174293037)
    (by decide : 174293037 ≤ 174325805) block2 block3

theorem join_1_0 : (twinPrimeSegment 174194733 174325805).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 174194733 ≤ 174260269)
    (by decide : 174260269 ≤ 174325805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174194733 174325805).card = 482 := join_1_0

end S083C01
end Sude.GeneratedTwinScan
