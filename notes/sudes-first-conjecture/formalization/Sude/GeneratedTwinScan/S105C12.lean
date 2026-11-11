import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14893)) 221773869 221806637 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 221773869 221806637).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14893 221773869 221806637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14894)) 221806637 221839405 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 221806637 221839405).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14894 221806637 221839405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14895)) 221839405 221872173 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 221839405 221872173).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14895 221839405 221872173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14896)) 221872173 221904941 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 221872173 221904941).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14896 221872173 221904941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 221773869 221839405).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 221773869 ≤ 221806637)
    (by decide : 221806637 ≤ 221839405) block0 block1

theorem join_0_1 : (twinPrimeSegment 221839405 221904941).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 221839405 ≤ 221872173)
    (by decide : 221872173 ≤ 221904941) block2 block3

theorem join_1_0 : (twinPrimeSegment 221773869 221904941).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 221773869 ≤ 221839405)
    (by decide : 221839405 ≤ 221904941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 221773869 221904941).card = 466 := join_1_0

end S105C12
end Sude.GeneratedTwinScan
