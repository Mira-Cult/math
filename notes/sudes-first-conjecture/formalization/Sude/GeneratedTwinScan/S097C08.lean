import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14300)) 204472365 204505133 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204472365 204505133).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14300 204472365 204505133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14301)) 204505133 204537901 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204505133 204537901).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14301 204505133 204537901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14302)) 204537901 204570669 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204537901 204570669).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14302 204537901 204570669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14303)) 204570669 204603437 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204570669 204603437).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14303 204570669 204603437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204472365 204537901).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 204472365 ≤ 204505133)
    (by decide : 204505133 ≤ 204537901) block0 block1

theorem join_0_1 : (twinPrimeSegment 204537901 204603437).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 204537901 ≤ 204570669)
    (by decide : 204570669 ≤ 204603437) block2 block3

theorem join_1_0 : (twinPrimeSegment 204472365 204603437).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 204472365 ≤ 204537901)
    (by decide : 204537901 ≤ 204603437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204472365 204603437).card = 477 := join_1_0

end S097C08
end Sude.GeneratedTwinScan
