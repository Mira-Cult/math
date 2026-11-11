import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21324)) 454688813 454721581 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 454688813 454721581).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21324 454688813 454721581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21324)) 454721581 454754349 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 454721581 454754349).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21324 454721581 454754349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21325)) 454754349 454787117 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 454754349 454787117).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21325 454754349 454787117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21326)) 454787117 454819885 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 454787117 454819885).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21326 454787117 454819885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 454688813 454754349).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 454688813 ≤ 454721581)
    (by decide : 454721581 ≤ 454754349) block0 block1

theorem join_0_1 : (twinPrimeSegment 454754349 454819885).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 454754349 ≤ 454787117)
    (by decide : 454787117 ≤ 454819885) block2 block3

theorem join_1_0 : (twinPrimeSegment 454688813 454819885).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 454688813 ≤ 454754349)
    (by decide : 454754349 ≤ 454819885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 454688813 454819885).card = 443 := join_1_0

end S216C13
end Sude.GeneratedTwinScan
