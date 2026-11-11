import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21599)) 466485293 466518061 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 466485293 466518061).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21599 466485293 466518061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21599)) 466518061 466550829 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 466518061 466550829).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21599 466518061 466550829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21600)) 466550829 466583597 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 466550829 466583597).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21600 466550829 466583597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21601)) 466583597 466616365 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 466583597 466616365).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21601 466583597 466616365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 466485293 466550829).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 466485293 ≤ 466518061)
    (by decide : 466518061 ≤ 466550829) block0 block1

theorem join_0_1 : (twinPrimeSegment 466550829 466616365).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 466550829 ≤ 466583597)
    (by decide : 466583597 ≤ 466616365) block2 block3

theorem join_1_0 : (twinPrimeSegment 466485293 466616365).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 466485293 ≤ 466550829)
    (by decide : 466550829 ≤ 466616365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 466485293 466616365).card = 445 := join_1_0

end S222C07
end Sude.GeneratedTwinScan
