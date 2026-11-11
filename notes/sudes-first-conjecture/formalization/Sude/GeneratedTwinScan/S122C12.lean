import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16045)) 257425453 257458221 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 257425453 257458221).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16045 257425453 257458221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16046)) 257458221 257490989 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 257458221 257490989).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16046 257458221 257490989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16047)) 257490989 257523757 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 257490989 257523757).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16047 257490989 257523757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16048)) 257523757 257556525 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 257523757 257556525).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16048 257523757 257556525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 257425453 257490989).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 257425453 ≤ 257458221)
    (by decide : 257458221 ≤ 257490989) block0 block1

theorem join_0_1 : (twinPrimeSegment 257490989 257556525).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 257490989 ≤ 257523757)
    (by decide : 257523757 ≤ 257556525) block2 block3

theorem join_1_0 : (twinPrimeSegment 257425453 257556525).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 257425453 ≤ 257490989)
    (by decide : 257490989 ≤ 257556525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 257425453 257556525).card = 445 := join_1_0

end S122C12
end Sude.GeneratedTwinScan
