import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S146C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17521)) 306970669 307003437 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 306970669 307003437).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17521 306970669 307003437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17522)) 307003437 307036205 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 307003437 307036205).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17522 307003437 307036205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17523)) 307036205 307068973 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 307036205 307068973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17523 307036205 307068973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17524)) 307068973 307101741 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 307068973 307101741).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17524 307068973 307101741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 306970669 307036205).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 306970669 ≤ 307003437)
    (by decide : 307003437 ≤ 307036205) block0 block1

theorem join_0_1 : (twinPrimeSegment 307036205 307101741).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 307036205 ≤ 307068973)
    (by decide : 307068973 ≤ 307101741) block2 block3

theorem join_1_0 : (twinPrimeSegment 306970669 307101741).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 306970669 ≤ 307036205)
    (by decide : 307036205 ≤ 307101741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 306970669 307101741).card = 479 := join_1_0

end S146C06
end Sude.GeneratedTwinScan
