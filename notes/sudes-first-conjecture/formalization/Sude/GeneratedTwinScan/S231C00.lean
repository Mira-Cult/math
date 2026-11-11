import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22010)) 484442157 484474925 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484442157 484474925).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22010 484442157 484474925
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22011)) 484474925 484507693 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484474925 484507693).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22011 484474925 484507693
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22012)) 484507693 484540461 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484507693 484540461).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22012 484507693 484540461
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22013)) 484540461 484573229 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484540461 484573229).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22013 484540461 484573229
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484442157 484507693).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 484442157 ≤ 484474925)
    (by decide : 484474925 ≤ 484507693) block0 block1

theorem join_0_1 : (twinPrimeSegment 484507693 484573229).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 484507693 ≤ 484540461)
    (by decide : 484540461 ≤ 484573229) block2 block3

theorem join_1_0 : (twinPrimeSegment 484442157 484573229).card = 404 := by
  simpa using combineTwinPrimeSegments (by decide : 484442157 ≤ 484507693)
    (by decide : 484507693 ≤ 484573229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484442157 484573229).card = 404 := join_1_0

end S231C00
end Sude.GeneratedTwinScan
