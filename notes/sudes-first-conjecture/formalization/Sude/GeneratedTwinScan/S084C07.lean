import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13308)) 177078317 177111085 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177078317 177111085).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13308 177078317 177111085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13309)) 177111085 177143853 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177111085 177143853).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13309 177111085 177143853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13310)) 177143853 177176621 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177143853 177176621).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13310 177143853 177176621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13312)) 177176621 177209389 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177176621 177209389).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13312 177176621 177209389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177078317 177143853).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 177078317 ≤ 177111085)
    (by decide : 177111085 ≤ 177143853) block0 block1

theorem join_0_1 : (twinPrimeSegment 177143853 177209389).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 177143853 ≤ 177176621)
    (by decide : 177176621 ≤ 177209389) block2 block3

theorem join_1_0 : (twinPrimeSegment 177078317 177209389).card = 478 := by
  simpa using combineTwinPrimeSegments (by decide : 177078317 ≤ 177143853)
    (by decide : 177143853 ≤ 177209389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177078317 177209389).card = 478 := join_1_0

end S084C07
end Sude.GeneratedTwinScan
