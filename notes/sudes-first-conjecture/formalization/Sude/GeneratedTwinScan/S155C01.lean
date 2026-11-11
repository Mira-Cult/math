import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18033)) 325189677 325222445 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 325189677 325222445).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18033 325189677 325222445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18034)) 325222445 325255213 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 325222445 325255213).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18034 325222445 325255213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18035)) 325255213 325287981 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 325255213 325287981).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18035 325255213 325287981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18036)) 325287981 325320749 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 325287981 325320749).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18036 325287981 325320749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 325189677 325255213).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 325189677 ≤ 325222445)
    (by decide : 325222445 ≤ 325255213) block0 block1

theorem join_0_1 : (twinPrimeSegment 325255213 325320749).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 325255213 ≤ 325287981)
    (by decide : 325287981 ≤ 325320749) block2 block3

theorem join_1_0 : (twinPrimeSegment 325189677 325320749).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 325189677 ≤ 325255213)
    (by decide : 325255213 ≤ 325320749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 325189677 325320749).card = 456 := join_1_0

end S155C01
end Sude.GeneratedTwinScan
