import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22309)) 497680429 497713197 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497680429 497713197).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22309 497680429 497713197
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22310)) 497713197 497745965 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497713197 497745965).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22310 497713197 497745965
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22310)) 497745965 497778733 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497745965 497778733).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22310 497745965 497778733
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22311)) 497778733 497811501 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497778733 497811501).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22311 497778733 497811501
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497680429 497745965).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 497680429 ≤ 497713197)
    (by decide : 497713197 ≤ 497745965) block0 block1

theorem join_0_1 : (twinPrimeSegment 497745965 497811501).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 497745965 ≤ 497778733)
    (by decide : 497778733 ≤ 497811501) block2 block3

theorem join_1_0 : (twinPrimeSegment 497680429 497811501).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 497680429 ≤ 497745965)
    (by decide : 497745965 ≤ 497811501) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497680429 497811501).card = 427 := join_1_0

end S237C05
end Sude.GeneratedTwinScan
