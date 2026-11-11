import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13853)) 191889453 191922221 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191889453 191922221).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13853 191889453 191922221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13854)) 191922221 191954989 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191922221 191954989).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13854 191922221 191954989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13855)) 191954989 191987757 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191954989 191987757).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13855 191954989 191987757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13857)) 191987757 192020525 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191987757 192020525).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13857 191987757 192020525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191889453 191954989).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 191889453 ≤ 191922221)
    (by decide : 191922221 ≤ 191954989) block0 block1

theorem join_0_1 : (twinPrimeSegment 191954989 192020525).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 191954989 ≤ 191987757)
    (by decide : 191987757 ≤ 192020525) block2 block3

theorem join_1_0 : (twinPrimeSegment 191889453 192020525).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 191889453 ≤ 191954989)
    (by decide : 191954989 ≤ 192020525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191889453 192020525).card = 468 := join_1_0

end S091C08
end Sude.GeneratedTwinScan
