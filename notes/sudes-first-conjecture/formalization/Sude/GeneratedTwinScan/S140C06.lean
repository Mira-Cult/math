import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17158)) 294387757 294420525 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 294387757 294420525).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17158 294387757 294420525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17159)) 294420525 294453293 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294420525 294453293).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17159 294420525 294453293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17160)) 294453293 294486061 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294453293 294486061).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17160 294453293 294486061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17161)) 294486061 294518829 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 294486061 294518829).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17161 294486061 294518829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 294387757 294453293).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 294387757 ≤ 294420525)
    (by decide : 294420525 ≤ 294453293) block0 block1

theorem join_0_1 : (twinPrimeSegment 294453293 294518829).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 294453293 ≤ 294486061)
    (by decide : 294486061 ≤ 294518829) block2 block3

theorem join_1_0 : (twinPrimeSegment 294387757 294518829).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 294387757 ≤ 294453293)
    (by decide : 294453293 ≤ 294518829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 294387757 294518829).card = 450 := join_1_0

end S140C06
end Sude.GeneratedTwinScan
