import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16086)) 258736173 258768941 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258736173 258768941).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16086 258736173 258768941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16087)) 258768941 258801709 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258768941 258801709).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16087 258768941 258801709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16088)) 258801709 258834477 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258801709 258834477).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16088 258801709 258834477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16089)) 258834477 258867245 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258834477 258867245).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16089 258834477 258867245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258736173 258801709).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 258736173 ≤ 258768941)
    (by decide : 258768941 ≤ 258801709) block0 block1

theorem join_0_1 : (twinPrimeSegment 258801709 258867245).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 258801709 ≤ 258834477)
    (by decide : 258834477 ≤ 258867245) block2 block3

theorem join_1_0 : (twinPrimeSegment 258736173 258867245).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 258736173 ≤ 258801709)
    (by decide : 258801709 ≤ 258867245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258736173 258867245).card = 473 := join_1_0

end S123C06
end Sude.GeneratedTwinScan
