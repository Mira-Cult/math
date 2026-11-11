import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22235)) 494403629 494436397 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494403629 494436397).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22235 494403629 494436397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22236)) 494436397 494469165 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494436397 494469165).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22236 494436397 494469165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22237)) 494469165 494501933 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494469165 494501933).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22237 494469165 494501933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22238)) 494501933 494534701 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494501933 494534701).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22238 494501933 494534701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494403629 494469165).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 494403629 ≤ 494436397)
    (by decide : 494436397 ≤ 494469165) block0 block1

theorem join_0_1 : (twinPrimeSegment 494469165 494534701).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 494469165 ≤ 494501933)
    (by decide : 494501933 ≤ 494534701) block2 block3

theorem join_1_0 : (twinPrimeSegment 494403629 494534701).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 494403629 ≤ 494469165)
    (by decide : 494469165 ≤ 494534701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494403629 494534701).card = 414 := join_1_0

end S235C12
end Sude.GeneratedTwinScan
