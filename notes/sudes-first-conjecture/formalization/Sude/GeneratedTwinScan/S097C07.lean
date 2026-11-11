import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14295)) 204341293 204374061 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204341293 204374061).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14295 204341293 204374061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14297)) 204374061 204406829 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204374061 204406829).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14297 204374061 204406829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14298)) 204406829 204439597 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204406829 204439597).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14298 204406829 204439597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14299)) 204439597 204472365 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204439597 204472365).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14299 204439597 204472365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204341293 204406829).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 204341293 ≤ 204374061)
    (by decide : 204374061 ≤ 204406829) block0 block1

theorem join_0_1 : (twinPrimeSegment 204406829 204472365).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 204406829 ≤ 204439597)
    (by decide : 204439597 ≤ 204472365) block2 block3

theorem join_1_0 : (twinPrimeSegment 204341293 204472365).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 204341293 ≤ 204406829)
    (by decide : 204406829 ≤ 204472365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204341293 204472365).card = 483 := join_1_0

end S097C07
end Sude.GeneratedTwinScan
