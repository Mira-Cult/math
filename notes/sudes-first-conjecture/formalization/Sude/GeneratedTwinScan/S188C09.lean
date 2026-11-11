import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19886)) 395444269 395477037 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395444269 395477037).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19886 395444269 395477037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19887)) 395477037 395509805 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 395477037 395509805).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19887 395477037 395509805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19888)) 395509805 395542573 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 395509805 395542573).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19888 395509805 395542573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19889)) 395542573 395575341 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395542573 395575341).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19889 395542573 395575341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395444269 395509805).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 395444269 ≤ 395477037)
    (by decide : 395477037 ≤ 395509805) block0 block1

theorem join_0_1 : (twinPrimeSegment 395509805 395575341).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 395509805 ≤ 395542573)
    (by decide : 395542573 ≤ 395575341) block2 block3

theorem join_1_0 : (twinPrimeSegment 395444269 395575341).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 395444269 ≤ 395509805)
    (by decide : 395509805 ≤ 395575341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395444269 395575341).card = 420 := join_1_0

end S188C09
end Sude.GeneratedTwinScan
