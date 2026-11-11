import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18088)) 327155757 327188525 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327155757 327188525).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18088 327155757 327188525
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18089)) 327188525 327221293 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327188525 327221293).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18089 327188525 327221293
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18090)) 327221293 327254061 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327221293 327254061).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18090 327221293 327254061
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18091)) 327254061 327286829 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327254061 327286829).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18091 327254061 327286829
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327155757 327221293).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 327188525)
    (by decide : 327188525 ≤ 327221293) block0 block1

theorem join_0_1 : (twinPrimeSegment 327221293 327286829).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 327221293 ≤ 327254061)
    (by decide : 327254061 ≤ 327286829) block2 block3

theorem join_1_0 : (twinPrimeSegment 327155757 327286829).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 327155757 ≤ 327221293)
    (by decide : 327221293 ≤ 327286829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327155757 327286829).card = 418 := join_1_0

end S156C00
end Sude.GeneratedTwinScan
