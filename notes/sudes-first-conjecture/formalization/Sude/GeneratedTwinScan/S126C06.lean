import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16280)) 265027629 265060397 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265027629 265060397).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16280 265027629 265060397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16281)) 265060397 265093165 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265060397 265093165).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16281 265060397 265093165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16282)) 265093165 265125933 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 265093165 265125933).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16282 265093165 265125933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16283)) 265125933 265158701 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 265125933 265158701).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16283 265125933 265158701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265027629 265093165).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 265027629 ≤ 265060397)
    (by decide : 265060397 ≤ 265093165) block0 block1

theorem join_0_1 : (twinPrimeSegment 265093165 265158701).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 265093165 ≤ 265125933)
    (by decide : 265125933 ≤ 265158701) block2 block3

theorem join_1_0 : (twinPrimeSegment 265027629 265158701).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 265027629 ≤ 265093165)
    (by decide : 265093165 ≤ 265158701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265027629 265158701).card = 448 := join_1_0

end S126C06
end Sude.GeneratedTwinScan
