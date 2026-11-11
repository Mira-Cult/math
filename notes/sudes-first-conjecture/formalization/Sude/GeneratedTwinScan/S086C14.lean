import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13498)) 182190125 182222893 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182190125 182222893).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13498 182190125 182222893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13500)) 182222893 182255661 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 182222893 182255661).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13500 182222893 182255661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13501)) 182255661 182288429 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 182255661 182288429).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13501 182255661 182288429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13502)) 182288429 182321197 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 182288429 182321197).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13502 182288429 182321197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182190125 182255661).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 182190125 ≤ 182222893)
    (by decide : 182222893 ≤ 182255661) block0 block1

theorem join_0_1 : (twinPrimeSegment 182255661 182321197).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 182255661 ≤ 182288429)
    (by decide : 182288429 ≤ 182321197) block2 block3

theorem join_1_0 : (twinPrimeSegment 182190125 182321197).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 182190125 ≤ 182255661)
    (by decide : 182255661 ≤ 182321197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182190125 182321197).card = 468 := join_1_0

end S086C14
end Sude.GeneratedTwinScan
