import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16927)) 286523437 286556205 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286523437 286556205).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16927 286523437 286556205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16928)) 286556205 286588973 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286556205 286588973).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16928 286556205 286588973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16929)) 286588973 286621741 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286588973 286621741).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16929 286588973 286621741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16930)) 286621741 286654509 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286621741 286654509).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16930 286621741 286654509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286523437 286588973).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 286523437 ≤ 286556205)
    (by decide : 286556205 ≤ 286588973) block0 block1

theorem join_0_1 : (twinPrimeSegment 286588973 286654509).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 286588973 ≤ 286621741)
    (by decide : 286621741 ≤ 286654509) block2 block3

theorem join_1_0 : (twinPrimeSegment 286523437 286654509).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 286523437 ≤ 286588973)
    (by decide : 286588973 ≤ 286654509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286523437 286654509).card = 452 := join_1_0

end S136C10
end Sude.GeneratedTwinScan
